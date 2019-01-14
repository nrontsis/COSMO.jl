# ---------------------------
# STRUCTS
# ---------------------------
mutable struct SparsityPattern
  g::Graph
  sntree::SuperNodeTree

  # constructor for sparsity pattern
  function SparsityPattern(rows::Array{Int64,1}, N::Int64, NONZERO_FLAG::Bool)
    g = Graph(rows, N, NONZERO_FLAG)
    sntree = SuperNodeTree(g)
    return new(g, sntree)
  end

end

# ---------------------------
# FUNCTIONS
# ---------------------------
function _contains(convex_sets::COSMO.CompositeConvexSet, t::Type{<:COSMO.AbstractConvexCone})
  for set in convex_sets.sets
    if typeof(set) == t
      return true
    end
  end
  return false
end

function num_ssets(convex_sets::Array{CompositeConvexSet}, t::Type{<:CompositeConvexSet})
  number = 0
  for set in convex_sets
    typeof(set) == t && (number += 1)
  end
  return number
end

# function shift_indices!(convex_sets::Array{CompositeConvexSet}, shift::Int64)
#   for set in convex_sets
#       set.indices = (set.indices.start + shift):(set.indices.stop + shift)
#   end
# end

function chordal_decomposition!(ws::COSMO.Workspace)
  ws.ci = ChordalInfo{Float64}(ws.p)
  settings = ws.settings
  problem = ws.p

  # do nothing if no psd cones present in the problem
  if !_contains(problem.C, PsdCone{Float64})
    settings.decompose = false
    return nothing
  end
  # Store the indices of the psd cones in psd_cones_ind
  indices = get_set_indices(problem.C.sets)
  psd_cones_ind = indices[findall(x -> typeof(x) == PsdCone{Float64}, problem.C.sets)]

  # find sparsity pattern for each cone
  sp_arr = Array{COSMO.SparsityPattern}(undef, length(psd_cones_ind))

  # find sparsity pattern, graphs, and clique sets for each cone
  for (iii,ind) in enumerate(psd_cones_ind)
    csp = find_aggregate_sparsity(problem.A, problem.b, ind)
    cDim = Int(sqrt(ind.stop - ind.start + 1))
    sp_arr[iii] = COSMO.SparsityPattern(csp, cDim, true)
  end

  # find transformation matrix H and store it
  H, decomposed_psd_cones = find_stacking_matrix(psd_cones_ind, sp_arr, problem.model_size[1])
  ws.ci.H = H

  # augment the system
  m,n = size(problem.A)
  mH,nH = size(H)
  @show(m,n,mH,nH)
  problem.P = blockdiag(problem.P, spzeros(nH, nH))
  problem.q = vec([problem.q; zeros(nH)])
  problem.A = [problem.A H; spzeros(nH, n) -sparse(1.0I, nH, nH)]
  problem.b = vec([problem.b; zeros(nH)])
  problem.model_size[1] = size(problem.A, 1)
  problem.model_size[2] = size(problem.A, 2)

  filtered_cones = filter(x -> typeof(x) != PsdCone{Float64}, problem.C.sets)
  new_composite_convex_set = Array{AbstractConvexSet{Float64}}([COSMO.ZeroSet{Float64}(mH); filtered_cones; decomposed_psd_cones])
  problem.C = COSMO.CompositeConvexSet(new_composite_convex_set)

  # increase the variable dimension
  ws.vars = Variables{Float64}(problem.model_size[1], problem.model_size[2], problem.C)

  nothing
end

# find the zero rows of a sparse matrix a
function zero_rows(a::SparseMatrixCSC, DROP_ZEROS_FLAG::Bool)
    DROP_ZEROS_FLAG && dropzeros!(a)
    passive = trues(a.m)
    for r in a.rowval
        passive[r] = false
    end
    return findall(passive)
end

function nz_rows(a::SparseMatrixCSC, ind::UnitRange{Int64}, DROP_ZEROS_FLAG::Bool)
    DROP_ZEROS_FLAG && dropzeros!(a)
    active = falses(length(ind))
    for r in a.rowval
      if in(r, ind)
        active[r] = true
      end
    end
    return findall(active)
end

function number_of_overlaps_in_rows(A::SparseMatrixCSC)
  # sum the entries row-wise
  numOverlaps = sum(A, dims=2)
  ri = findall(x -> x > 1, numOverlaps)
  return ri, numOverlaps[ri]
end

function find_aggregate_sparsity(A, b, ind)
  AInd = nz_rows(A, ind, false)
  # commonZeros = AInd[find(x->x==0,b[AInd])]
  bInd = findall(x -> x != 0, view(b, ind))
  commonNZeros = union(AInd, bInd)
  return commonNZeros
end

function find_aggregate_sparsity(Asub, bsub)
  m,n = size(Asub)
  AInd = zero_rows(Asub, false)
  commonZeros = AInd[find( x -> x == 0, b[AInd])]
  mSize = Int(sqrt(m))
  csp = spzeros(Int64, mSize, mSize)
  csp[:,:] = 1

  for ind in commonZeros
    i, j = vec_to_mat_ind(ind, mSize)
    csp[i, j] = 0
  end
  return csp
end

function vec_to_mat_ind(ind::Int64, n::Int64)
  ind > n^2 && error("Index ind out of range.")
  ind == 1 && (return 1, 1)

  r = ind % n

  if r == 0
    j = Int(ind / n)
    i = n
  else
    j = Int(floor(ind / n) + 1)
    i = r
  end
  return i, j
end


# function getClique(cs::CliqueSet,ind::Int64)
#   len = length(cs.cliqueInd)
#   ind > len && error("Clique index ind=$(ind) is higher than number of cliques in the provided set:$(len).")
#   ind < len ? (c = cs.cliques[cs.cliqueInd[ind]:cs.cliqueInd[ind+1]-1]) : (c = cs.cliques[cs.cliqueInd[ind]:end])
#   return c
# end

# function finds the transformation matrix H to decompose the vector s into its parts and stacks them into sbar, also returns  Ks
function find_stacking_matrix(psd_cones_ind::Array{UnitRange{Int64},1}, sp_arr::Array{SparsityPattern,1}, m::Int64)

  num_cones = length(psd_cones_ind)
  num_cones != length(sp_arr) && error("Number of psd cones and number of clique sets don't match.")

  stacked_sizes = zeros(Int64, num_cones)
  for iii=1:num_cones
    stacked_sizes[iii] = sum(sp_arr[iii].sntree.nBlk)
  end

  bK = m - sum(map(x -> length(x), psd_cones_ind))

  # length of stacked vector sbar
  n = bK + sum(stacked_sizes)

  H = spzeros(m, n)
  H[1:bK,1:bK] = sparse(1.0I, bK, bK)
  bK += 1
  b = bK
  decomposed_psd_cones = Array{COSMO.PsdCone}(undef, 0)
  # loop over all supernode trees that hold the clique information for each decomposed cone
  for kkk = 1:length(sp_arr)
    sntree = sp_arr[kkk].sntree
    mH = Int64
    for iii=1:getNumCliques(sntree)
      # new stacked size
      mk = Int(sqrt(sntree.nBlk[iii]))
      # original size
      nk = Int(sqrt(length(psd_cones_ind[kkk])))
      Ek = zeros(mk, nk)
      c = get_clique(sntree, iii)
      sort!(c)
      for (jjj, v) in enumerate(c)
        Ek[jjj, v] = 1
      end
      Hkt = (kron(Ek, Ek))'
      mH, nH = size(Hkt)
      H[b:b + mH - 1, bK:bK + nH - 1] = Hkt
      # create new cone and push to decomposedCone Array
      push!(decomposed_psd_cones, COSMO.PsdCone(nH))
      bK += nH
    end
    b += mH
  end
  return H, decomposed_psd_cones

end

function reverse_decomposition!(ws::COSMO.Workspace, settings::COSMO.Settings)
  mO = ws.ci.originalM
  nO = ws.ci.originalN

  H = ws.ci.H

  vars = Variables{Float64}(mO, nO, ws.ci.originalC)
  vars.x .= ws.vars.x[1:nO]
  vars.s  .= SplitVector{Float64}(H * ws.vars.s[mO + 1:end], ws.ci.originalC)

  # fill dual variables such that μ_k  = H_k μ for k=1,...,p
  fill_dual_variables!(ws, vars)

  # if user requests, perform positive semidefinite completion on entries of μ that were not in the decomposed blocks
  settings.complete_dual && psd_completion!(ws, vars)

  ws.vars = vars
  ws.p.C = ws.ci.originalC
  return nothing
end

function fill_dual_variables!(ws::COSMO.Workspace,vars::Variables)
  mO = ws.ci.originalM
  H = ws.ci.H

  # this performs the operation μ = sum H_k^T *  μ_k causing an addition of (identical valued) overlapping blocks
  vars.μ .= H * ws.vars.μ[mO + 1:end]

  # to remove the overlaps we take the average of the values for each overlap by dividing by the number of blocks that overlap in a particular entry, i.e. number of 1s in each row of H
  rowInd,nnzs = number_of_overlaps_in_rows(H)

  for iii=1:length(rowInd)
    ri = rowInd[iii]
    vars.μ[ri] .= ws.vars.μ[ri] / nnzs[iii]
  end
end

# complete the dual variable
function psd_completion!(ws::COSMO.Workspace)
  return nothing
end
