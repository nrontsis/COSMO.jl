
# -------------------------------------
# abstract type defs
# -------------------------------------
abstract type AbstractKKTSolver end

# NB: all concrete examples of this type should
# implement refactor! and solve! methods and should
# implement a constructor taking (P,A,sigma,rho) as
# arguments

# -------------------------------------
# some internal utility functions
# -------------------------------------

function _kktutils_check_dims(P, A, sigma, rho)

    n = size(P, 1)
    m = size(A, 1)

    size(A,2) == n || throw(DimensionMismatch())

    length(rho)   == m || length(rho)   == 1 || throw(DimensionMismatch())
    length(sigma) == n || length(sigma) == 1 || throw(DimensionMismatch())

    return m, n
end

function _kktutils_make_kkt(P, A, sigma, rho, shape::Symbol=:F)

    S = length(sigma) == 1 ? (sigma[1]) * I : Diagonal(sigma)
    n = size(P, 1)
    m = size(A, 1)

    if length(rho) == 1
        rho = rho .* ones(m)
    end

    if     shape == :F
        #compute the full KKT matrix
        K = [P + S SparseMatrixCSC(A'); A -I]

    elseif shape == :U
        #upper triangular
        K = [triu(P) + S  SparseMatrixCSC(A'); spzeros(eltype(A), m, n)  -I]

    elseif shape == :L
        #lower triangular
        K = [tril(P)+S  spzeros(eltype(A), n, m); A  -I]

    else
        error("Bad matrix shape description")
    end

    @inbounds @simd for i = (n + 1):(n + m)
        K[i, i] = -1.0 / rho[i - n]
    end

    return K

end

#an index into a KKT matrix indicating where
#values of 1/rho should be placed
_kktutils_rho_index(K, m, n) = diagind(K, 0)[(n+1):(m+n)]




# -------------------------------------
# QDLDL solver
# -------------------------------------

struct QdldlKKTSolver <: AbstractKKTSolver

    m::Integer
    n::Integer
    ldlfact::QDLDL.QDLDLFactorisation

    function QdldlKKTSolver(P::SparseMatrixCSC, A::SparseMatrixCSC, sigma, rho)

        m,n = _kktutils_check_dims(P, A, sigma, rho)

        #NB: qdldl uses triu internally, but it reorders
        #with AMD first.  This way is memory inefficient
        #but saves having to permute the rhs/lhs each
        #time we solve.
        K   = _kktutils_make_kkt(P, A, sigma, rho, :F)
        ldlfact = qdldl(K)

        #check for exactly n positive eigenvalues
        positive_inertia(ldlfact) == n || error("Objective function is not convex.")

        new(m, n, ldlfact)
    end
end

function solve!(s::QdldlKKTSolver, lhs, rhs)
    lhs .= rhs
    QDLDL.solve!(s.ldlfact, lhs)
end


function update_rho!(s::QdldlKKTSolver, rho)
    QDLDL.update_diagonal!(s.ldlfact, (s.n+1):(s.n+s.m),(-1 ./ rho))
end

# -------------------------------------
# Julia Native solver (CHOLMOD based)
# -------------------------------------
mutable struct CholmodKKTSolver <: AbstractKKTSolver

    fact::SuiteSparse.CHOLMOD.Factor
    K::SparseMatrixCSC
    m::Integer
    n::Integer
    rhoidx::AbstractArray

    function CholmodKKTSolver(P::SparseMatrixCSC, A::SparseMatrixCSC, sigma, rho)

         m,n  = _kktutils_check_dims(P, A, sigma, rho)
         K    = _kktutils_make_kkt(P, A, sigma, rho, :F)
         fact = ldlt(K)
         rhoidx = _kktutils_rho_index(K, m, n)

        return new(fact, K, m, n, rhoidx)

    end
end

solve!(s::CholmodKKTSolver, lhs, rhs) = lhs .= s.fact \ rhs

function update_rho!(s::CholmodKKTSolver, rho)

    s.K[s.rhoidx] .= -1. ./ rho
    #complete restart
    s.fact = ldlt(s.K)

end

free_memory!(s::AbstractKKTSolver) = nothing

# Custom code for doubly stochastic
using LinearMaps, IterativeSolvers
import Base: getindex, size, *
import LinearAlgebra: mul!, ldiv!

mutable struct CustomConstraint{Tv} <: AbstractMatrix{Tv} 
    C::SparseMatrixCSC{Tv, Int}
    m::Int
    n::Int

    function CustomConstraint(C::SparseMatrixCSC{Tv}) where {Tv}
        new{Tv}(C, 2*size(C, 1) + length(C.nzval), length(C.nzval))
    end
end

size(M::CustomConstraint) = (M.m, M.n)
function size(M::CustomConstraint, i)
    if i == 1
        return M.m
    elseif i == 2
        return M.n
    end
end

*(C::CustomConstraint{Tv}, x::StridedVector{Tv}) where {Tv} = mul!(zeros(Tv, size(C, 1)), C, x)
*(adjC::Adjoint{<:Any, CustomConstraint{Tv}}, x::StridedVector{Tv}) where {Tv} = mul!(zeros(Tv, size(adjC, 1)), adjC, x)

function mul!(y::StridedVector{Tv}, C::CustomConstraint{Tv}, x::StridedVector{Tv}) where {Tv}
    nnz = length(C.C.nzval); n = size(C.C, 1)
    y1 = view(y, 1:nnz); y2 = view(y, nnz+1:nnz+2*n)
    y1 .= x
    mul_A!(y2, C.C, x)
    return y
end

function mul!(y::StridedVector{Tv}, adjC::Adjoint{<:Any, CustomConstraint{Tv}}, x::StridedVector{Tv}) where {Tv}
    C = adjC.parent
    nnz = length(C.C.nzval); n = size(C.C, 1)
    x1 = view(x, 1:nnz); x2 = view(x, nnz+1:nnz+2*n)
    mul_At!(y, C.C, x2)
    y .+= x1
    return y
end

function getindex(M::CustomConstraint, i::Int)
    @assert false
end

function getindex(M::CustomConstraint, i, j)
    @assert false
end
 

function mul_A!(y, C::SparseMatrixCSC, x)
    n = size(C, 1)

    y .= 0
    @inbounds for j in 1:n, idx in C.colptr[j]:C.colptr[j+1]-1
        i = C.rowval[idx]
        y[i] += x[idx]
        y[j + n] += x[idx]
    end

    return y
end

ldiv!(y::Array{T,1}, D::Diagonal{T,Array{Float64,1}}, x::Array{T,1}) where {T} = ldiv!(D, copyto!(y, x))

function mul_At!(y, C::SparseMatrixCSC, x)
    n = size(C, 1)
    y .= 0
    @inbounds for j in 1:n, idx in C.colptr[j]:C.colptr[j+1]-1
        i = C.rowval[idx]
        y[idx] += x[i] + x[j + n]
    end

    return y
end

mutable struct CustomSolver{T} <: COSMO.AbstractKKTSolver
    m::Integer
    n::Integer
    C::SparseMatrixCSC{T}
    Ct::SparseMatrixCSC{T}
    row_sum::Vector{T}
    col_sum::Vector{T}
    ρ1::T
    ρ2::T
    σ::T
    previous_cg_solution::Vector{T}
    counter::Int
    multiplications::Vector{Int}

    function CustomSolver(P::AbstractArray{T}, A::AbstractArray{T}, σ::T, ρ) where{T}
        n = size(A.C, 1)
        m = 2*n
        C = copy(A.C)
        C.nzval .= 1
        Ct = SparseMatrixCSC(C')

        if length(ρ) > 1
            @assert all(view(ρ, 1:length(C.nzval)) .== ρ[1]) "rho vector should have constant value across each constraint"
            @assert all(view(ρ, length(C.nzval)+1:length(ρ)) .== ρ[end]) "rho vector should have constant value across each constraint"
        end

        new{T}(m, n, C, Ct, 
            sum(Ct, dims=1)[:],
            sum(C, dims=1)[:],
            ρ[1], ρ[end], σ, zeros(T, 2*n), 1, zeros(Int, 1)
        )
    end
end

function mul_reduced_system!(y::StridedVector{T}, S::CustomSolver{T}, x::StridedVector{T}) where {T}
    # Performs
    # y = (1 + σ + ρ)x + ρAA'x
    # Which is equivalent to
    # y = (1 + σ + ρ)x + ρ| diag(S*1)      S    | |x1|
    #                     |      S'   diag(S'*1)| |x2|

    S.multiplications[end] += 1 #logging

    y1 = view(y, 1:S.n); y2 = view(y, S.n+1:2*S.n)
    x1 = view(x, 1:S.n); x2 = view(x, S.n+1:2*S.n)
    mul!(y1, S.C, x2)
    mul!(y2, S.Ct, x1)
    @. y1 += x1*S.row_sum
    @. y2 += x2*S.col_sum

    lmul!(S.ρ2, y)
    axpy!(1 + S.σ + S.ρ1, x, y)
end

function solve!(S::CustomSolver, y, x)
    # Solves
    # | (1 + σ)I     I      A'   |  |y1|     |x1|
    # |        I    -I/ρ    0    |  |y2|  =  |x2|
    # |        A     0     -I/ρ  |  |y3|     |x3|
    # x1/y1: R^nnz, x2/y2: R^nnz x3/y3: R^2n
    # where [y1; y2; y3] := y, [x1; x2; x3] := x 
    n = size(S.C, 1); nnz = length(S.C.nzval)
    x1 = view(x, 1:nnz); y1 = view(y, 1:nnz)
    x2 = view(x, nnz+1:2*nnz); y2 = view(y, nnz+1:2*nnz)
    x3 = view(x, 2*nnz+1:2*nnz+2*n); y3 = view(y, 2*nnz+1:2*nnz + 2*n)

    # y3 = ((1 + σ + ρ1)x + ρ2AA')\(ρ2 Α(x1 + ρ1*x2) - ρ2 (1 + ρ1 + σ)x3)
    @. y1 = S.ρ2*(x1 + S.ρ1*x2)
    mul_A!(y3, S.C, y1)
    @. y3 -= (1 + S.ρ1 + S.σ)*S.ρ2*x3
    L = LinearMap((y, x) -> mul_reduced_system!(y, S, x), 2*n; ismutating=true, issymmetric=true)
    initial_tol = norm(L*S.previous_cg_solution - y3)
    # Pl = factorize(diagm(0 => [S.row_sum; S.col_sum])) # Diagonal Preconditioner
    Pl = Identity()
    tol = 10/S.counter^2

    cg!(S.previous_cg_solution, L, y3, Pl=Pl, tol=tol/norm(y3), initially_zero=false) #, maxiter=10)
    # @assert tol > norm(L*S.previous_cg_solution - y3)
    copyto!(y3, S.previous_cg_solution)

    # y1 = (x1 + ρ1 x2 - A'y3)/(1 + ρ1 + σ)
    mul_At!(y1, S.C, y3)
    @. y1 = (-y1 + x1 + S.ρ1*x2)/(1 + S.ρ1 + S.σ)
    # y2 = ρ1 (y1 - x2)
    @. y2 = S.ρ1*(y1 - x2)

    S.counter += 1
    push!(S.multiplications, 0)

    return y
end

function update_rho!(S::CustomSolver, ρ)
    if length(ρ) > 1
        @assert all(view(ρ, 1:length(S.C.nzval)) .== ρ[1]) "rho vector should have constant value across each constraint"
        @assert all(view(ρ, length(S.C.nzval)+1:length(ρ)) .== ρ[end]) "rho vector should have constant value across each constraint"
    end

    S.ρ1 = ρ[1]
    S.ρ2 = ρ[end]
end