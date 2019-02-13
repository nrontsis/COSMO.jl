
mutable struct Graph
adjacencyList::Array{Array{Int64,1}}
ordering::Array{Int64} # σ(v) = i
reverse_ordering::Array{Int64} #σ^(-1)(i)

# constructor for sparse input matrix
# function Graph(A::Union{SparseMatrixCSC{Int64,Int64},SparseMatrixCSC{Float64,Int64}})
#   if A != A'
#     error("Input has to be a symmetric matrix.")
#   end
#   N = size(A,1)
#   ordering = collect(1:1:N)
#   adjacencyList = [Int64[] for i=1:N]
#   for j = 1:N-1
#     for i=j+1:N
#       if A[i,j] != 0
#         push!(adjacencyList[i],j)
#         push!(adjacencyList[j],i)
#       end
#     end
#   end
#   g = new(adjacencyList,ordering,[])
#   # make sure that the graph is connected
#   connectGraph!(g)
#   # make graph chordal
#   mcsmSearch!(g)
#   return g
# end

# # constructor for sparse input matrix
# function Graph(A::Union{SparseMatrixCSC{Int64,Int64},SparseMatrixCSC{Float64,Int64}},MCSM_FLAG::Bool)
#   if A != A'
#     error("Input has to be a symmetric matrix.")
#   end
#   N = size(A,1)
#   ordering = collect(1:1:N)
#   adjacencyList = [Int64[] for i=1:N]
#   for j = 1:N-1
#     for i=j+1:N
#       if A[i,j] != 0
#         push!(adjacencyList[i],j)
#         push!(adjacencyList[j],i)
#       end
#     end
#   end
#   g = new(adjacencyList,ordering,[])
#   mcsSearch!(g)
#   return g
# end

function Graph(aL, o, ro)
  return new(aL, o, ro)
end

# constructor for list of zero or nonzero rows of vectorized matrix
function Graph(rows::Array{Int64,1}, N::Int64, NONZERO_FLAG::Bool)
  # determine number of vertices of graph N
  ordering = collect(1:1:N)
  adjacency_list = [Int64[] for i=1:N]

  row_val, col_val = row_ind_to_matrix_indices(rows, N)
  F = QDLDL.qdldl(sparse(row_val, col_val, ones(length(row_val))), perm= nothing,logical = true)
 # ordering = F.p
  ordering = collect(1:N)
  lower_triangle_to_adjacency_list!(adjacency_list, F.L)

  # make sure that the graph is connected
  # FIXME: Relevant check?
  # connectGraph!(g)
  reverse_ordering = zeros(size(ordering, 1))
  for i = 1:N
    reverse_ordering[Int64(ordering[i])] = i
  end

  g = new(adjacency_list, ordering, reverse_ordering)

  return g
end
end

# -------------------------------------
# FUNCTION DEFINITIONS
# -------------------------------------

# function to compare two graphs based on their adjacencylist
function equalGraphs(g1,g2)
for iii=1:length(g1.adjacencyList)
if g1.adjacencyList[iii] != g2.adjacencyList[iii]
  return false
end
end
return true
end

# deepcopy function for Graph struct
function Base.deepcopy(g::Graph)
return Graph(deepcopy(g.adjacencyList), deepcopy(g.ordering), deepcopy(g.reverse_ordering))
end

# Redefinition of the show function that fires when the object is called
function Base.show(io::IO, obj::Graph)
println(io,"\nGraph:\nAdjacency List:")

# only print out information if Graph is small enough
if length(obj.adjacencyList) <= 15
  for i=1:size(obj.adjacencyList,1)
    println(io,"Vertex $(i): $(obj.adjacencyList[i])")
  end
  println(io,"\nOrdering σ(v) = i: $(obj.ordering)")
  println(io,"Reverse Ordering σ^-1(i) = v: $(obj.reverse_ordering)\n")
end
println(io,"\nNumber of vertices: $(length(obj.adjacencyList))\nNumber of edges: $(sum(map(x->length(x),obj.adjacencyList))/2)")
end


function numberOfVertices(g::Graph)
return size(g.ordering,1)
end

# returns the neighbor with the lowest order higher than the nodes order
function findParent(g::Graph,higherNeighbors::Array{Int64})
if size(higherNeighbors,1) > 0
  return higherNeighbors[indmin(g.ordering[higherNeighbors])]
else
  return 0
end
end

# findall the cardinality of adj+(v) for all v in V
function higherDegrees(g::Graph)
  N = length(g.adjacencyList)
  degrees = zeros(Int64,N)
  for iii = 1:N
      order = g.ordering[iii]
      degrees[iii] = length(filter(x-> g.ordering[x] > order,g.adjacencyList[iii]))
  end
  return degrees
end




function findHigherNeighbors(g::Graph,nodeNumber::Int64)
order = g.ordering[nodeNumber]
neighbors = g.adjacencyList[nodeNumber]
higherNeighbors = neighbors[findall(f->f>order,g.ordering[neighbors])]
return higherNeighbors
end

function findHigherNeighborsSorted(g::Graph,nodeNumber::Int64,ordering::Array{Int64,1})
order = ordering[nodeNumber]
neighbors = g.adjacencyList[nodeNumber]
higherNeighbors = neighbors[findall(f->f>order,ordering[neighbors])]
sort!(higherNeighbors, by=x->ordering[x])
return higherNeighbors
end

# performs a maximum cardinality search and updates the ordering to the graph (only perfect elim. ordering if graph is chordal)
function mcsSearch!(g::Graph)
N = numberOfVertices(g)
weights = zeros(N)
unvisited = ones(N)
perfectOrdering = zeros(N)
for i = N:-1:1
  # findall unvisited vertex of maximum weight
  unvisited_weights = weights.*unvisited
  indMax = indmax(unvisited_weights)
  perfectOrdering[indMax] = i
  unvisited[indMax] = 0
  for neighbor in g.adjacencyList[indMax]
    if unvisited[neighbor] == 1
      weights[neighbor]+=1
    end
  end
end
# update ordering of graph
g.ordering = perfectOrdering
reverse_ordering = zeros(size(perfectOrdering,1))
# also compute reverse order σ^-1(v)
for i = 1:N
  reverse_ordering[Int64(perfectOrdering[i])] = i
end
g.reverse_ordering = reverse_ordering
return nothing
end

# implementation of the MCS-M algorithm (see. A. Berry - Maximum Cardinality Search for Computing Minimal Triangulations of Graphs) that findalls a minimal triangulation
function mcsmSearch!(g::Graph)
doPrint = false
# initialize edge set F of fill-in edges
F = Array{Int64}[]
N = numberOfVertices(g)
weights = zeros(Int64,N)
unvisited = ones(Int64,N)
perfectOrdering = zeros(Int64,N)
for i = N:-1:1
  # findall unvisited vertex of maximum weight
  unvisited_weights = weights.*unvisited
  v = argmax(unvisited_weights)
  perfectOrdering[v] = i

  doPrint && println(" >>> Pick next vertex: v = $(v) and assign order i=$(i)\n")
  # findall all unvisited Vertices u with a path u, x1, x2, ..., v in G, s.t. w(xi) < w(u) and put them in set S
  # in the first step there will be no valid path, therefore choose S to be the direct neighbors
  S = zeros(N)
  if i == N
    S[g.adjacencyList[v]] .= 1
  else
    if i > 1
      doPrint && println(" Dijkstra Search: v = $(v),  copy(unvisited)=$(copy(unvisited)),weights=$(weights)\n")
      S = dijkstra(g,v,copy(unvisited),weights,N)
      doPrint && println("S=$(S) of vertex $(v)\n")
    else
      S = zeros(N)
    end
  end
  unvisited[v] = 0
  # increment weight of all Vertices w and if w and v are no direct neighbors, add edges to F
  #weights[v] = 100
  for w in findall(x->x == 1,S)
    weights[w]+=1
    if !in(w,g.adjacencyList[v])
      push!(F,[w,v])
    end
  end
end
# update ordering of graph
g.ordering = perfectOrdering
# also compute reverse order σ^-1(v)
reverse_ordering = zeros(size(perfectOrdering,1))
for i = 1:N
  reverse_ordering[Int64(perfectOrdering[i])] = i
end
g.reverse_ordering = reverse_ordering

# TODO: Do other algorithms break if the adjacencylist is not ordered anymore? -> if so: sort adjacencylist
# make graph chordal by adding the new edges of F to E
for edge in F
  push!(g.adjacencyList[edge[1]],edge[2])
  push!(g.adjacencyList[edge[2]],edge[1])
end
return nothing
end

# modified dijkstra algorithm to findall for each vertex the minimum distance to v, where minimum distance means:
# - if one vertex on the path has been visited the distance will be set reasonably high
# - minimum distance is w = min(max(weight(x_i))) for all x_i in w,x1,x2,...,v
function dijkstra(g::Graph,v::Int64,unvisited::Array{Int64,1},weights::Array{Int64,1},N::Int64)
doPrint = false
distance = Inf*ones(Int64,N)
distance[v] = 0
weights[v] = 0
nodes = collect(1:N)
# loop over all Vertices
for iii = 1:N
  unvisitedNodes = filter(x->x !=-1,nodes)
  # pick unprocessed vertex with lowest distance-value
  u = unvisitedNodes[argmin(distance[unvisitedNodes])] #simplify!!!
  # dont bother with Vertices that already have an order
  if unvisited[u] == 1
    doPrint && println("--dijkstra:1,   iii=$(iii),Pick new: u=$(u) of distance=$(distance), unvisited=$(unvisited)\n")
    nodes[u] = -1 #flag that indicates that node has been visited
    doPrint && println("--dijkstra:2, Delete u: nodes=$(nodes), neighbors=$(g.adjacencyList[u])\n")
    # loop over all unvisited neighbors of u
    for w in g.adjacencyList[u]
      doPrint && println("--dijkstra:3, Loop through neighbors of u=$(u):  w=$(w) isinUnvisited?=$(in(w,nodes))\n")
      if nodes[w] != -1
        distanceUpdate(w,u,distance,weights,unvisited,N)
      end
    end
  else
    nodes[u] = -1
  end
end

# indicate with set S the Vertices that have a higher own weight than distance (flag set to 1)
S=zeros(N)
doPrint && println("--dijkstra:4,  Decide which S to add to S: weights=$(weights) distance=$(distance)\n")
# direct neighbors are always added to S
S[filter(x->unvisited[x] == 1,g.adjacencyList[v])] .= 1
for u in findall(x->x == 1, unvisited)
  if weights[u] > distance[u]
    S[u] = 1
  end
end
doPrint && ("--dijkstra:5,  S=$(S)")
return S
end

function distanceUpdate(w::Int64,u::Int64,distance::Array{Float64,1},weights::Array{Int64,1},unvisited::Array{Int64,1},N::Int64)
doPrint = false
doPrint && println("     --distanceUpdate:1, In: w=$(w) of u=$(u), distance[w]=$(distance[w]), distance[u]=$(distance[u]), weights[u]=$(weights[u])\n")
# if the vertex has already an order from a previous run of dijkstra() it can't be used as a valid path, hence make the distance reasonably high, ie. d=N
if unvisited[w] == 1
  alternative = max(distance[u],weights[u])
else
  alternative = N
end
if alternative < distance[w]
  distance[w] = alternative
end
doPrint && println("     --distanceUpdate:1, New distances of w=$(w) of u=$(u) distance[w]=$(distance[w])\n")
end


# returns lists of Vertices that form the unconnected subgraphs (breath-first-search style)
function getConnectedParts(g::Graph)
N = numberOfVertices(g)
subgraphs = []
visited = zeros(N)
allVisited = false

while !allVisited
  frontier = [findfirst(x->x== 0,visited)]
  visitedNodes = [frontier[1]]
  visited[frontier[1]] = 1
  while size(frontier,1) > 0
    nextFrontier = []
    for u in frontier
      for v in g.adjacencyList[u]
        if visited[v] == 0
          push!(visitedNodes,v)
          visited[v] = 1
          push!(nextFrontier,v)
        end
      end
    end
    frontier = nextFrontier
  end
  # add Vertices of subgraph to array
  push!(subgraphs,visitedNodes)

  # if all Vertices are processed break
  if !in(0,visited)
    allVisited = true
  end
end
return subgraphs
end

# connects an unconnected graph by adding edges
function connectGraph!(g::Graph)
subgraphs = getConnectedParts(g)

# if more than one subgraph are found, add one edge between the first node of each subgraph
if size(subgraphs,1) > 1
  for i=1:size(subgraphs,1)-1
    node_subgraphA = subgraphs[i][1]
    node_subgraphB = subgraphs[i+1][1]
    push!(g.adjacencyList[node_subgraphA],node_subgraphB)
    push!(g.adjacencyList[node_subgraphB],node_subgraphA)
  end
end
return nothing

end

# check if a graph is connected
function isConnected(g::Graph)
return size(getConnectedParts(g),1) == 1
end

# check if the ordering of the graph is a perfect elimination ordering (i.e. for every v, are all higher neighbors adjacent?)
# start with lowest-order vertex v, findall lowest neighbor u of v with higher order. Then verify that w is adjacent to all higher order neighbors of v
# Algorithm has running time O(m+n)
function isPerfectOrdering(g::Graph)
(length(g.reverse_ordering) == 0 || length(g.reverse_ordering) == 0) && error("Please provide graph with order and reverse order.")
for v in g.reverse_ordering
  higherNeighbors = findHigherNeighbors(g,v)
  if size(higherNeighbors,1) > 1
    u = higherNeighbors[indmin(g.ordering[higherNeighbors])]
    for w in higherNeighbors
      if w != u && !any(x->x==u,g.adjacencyList[w])
        return false
      end
    end
  end
end
return true
end

function row_ind_to_matrix_indices(rows::Array{Int64,1}, N::Int64)
  row_val = zeros(Int64, length(rows))
  col_val = zeros(Int64, length(rows))
  for (ind, r) in enumerate(rows)
        _rem = mod(r, N)
        fl = fld(r, N)
        if _rem == 0
          row_val[ind] = N
          col_val[ind] = fl
        else
          row_val[ind] = _rem
          col_val[ind] = fl + 1
         end
  end
  return row_val, col_val
end


function lower_triangle_to_adjacency_list!(alist::Array{Array{Int64,1},1}, L::SparseMatrixCSC{Float64, Int64})
  N = length(alist)
  j = 1
  for (ind, r) in enumerate(L.rowval)
    i = r
    if j != N && !(ind < L.colptr[j+1])
      j += 1
    end
    push!(alist[i], j)
    push!(alist[j], i)
 end

end


