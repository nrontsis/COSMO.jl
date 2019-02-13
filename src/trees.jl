
# -------------------------------------
# TYPE DEFINITIONS
# -------------------------------------
# mutable struct Node
#     value_top::Array{Int64,1}
#     value_btm::Array{Int64,1}
#     degree::Int64
#     parent::Int64
#     children::Array{Int64}
#     inSuperNode::Int64

#     # two constructor definitions
#     function Node(value_top::Array{Int64},value_btm::Array{Int64},degree::Int64,parent::Int64)
#         new(value_top,value_btm,degree,parent,[],0)
#     end

#     function Node(value_top::Array{Int64},value_btm::Array{Int64},degree::Int64,parent::Int64,children::Array{Int64})
#         new(value_top,value_btm,degree,parent,children,0)
#     end

# end

# mutable struct Tree
#     root::Int64
#     nodes::Array{Node}
#     order::Array{Int64}
#     reverseOrder::Array{Int64}
#     #constructor
#     function Tree()
#         new(0,Int64[],Int64[],Int64[])
#     end
# end

# # Redefinition of the show function that fires when the object is called
# function Base.show(io::IO, obj::Tree)
# println(io,"\nTree - Nodes:\nRoot: $(obj.root)\nOrder: $(obj.order)\n reverseOrder: $(obj.reverseOrder)")
# for node in obj.nodes
#     println("Node - Value_top: $(node.value_top), Value_btm: $(node.value_btm), Degree: $(node.degree), Parent: $(node.parent), Children: $(node.children), inSuperNode: $(node.inSuperNode)\n")
# end
# end


mutable struct SuperNodeTree
snd::Array{Int64,1} #vertices of supernodes stored in one array
snptr::Array{Int64,1} # vertices of supernode i are stored in snd[snptr[i]:snptr[i+1]-1]
snd_par::Array{Int64,1}  # parent of supernode k is supernode j=snd_par[k]
snd_post::Array{Int64,1} # post order of supernodal elimination tree
post::Array{Int64} # post ordering of the vertices in elim tree σ(j) = v
par::Array{Int64}
cliques::Array{Int64,1} #vertices of cliques stored in one array
chptr::Array{Int64,1} #points to the indizes where new clique starts in cliques array
nBlk::Array{Int64,1} #sizes of submatrizes defined by each clique
function SuperNodeTree(g::Graph)
    par = etree(g)
    child = childFromPar(par)
    post = postOrder(par,child)
    # faster algorithm according to Vandenberghe p.308
    degrees = higherDegrees(g)

    snd, snptr, snd_par = findSuperNodes(par,child,post,degrees)

    # TODO: amalgamate supernodes
    snd_child = childFromPar(snd_par)
    snd_post = postOrder(snd_par,snd_child)

    cliques,chptr,nBlk = findCliques(g,snd,snptr,snd_par,post)


    new(snd,snptr,snd_par,snd_post,post,par,cliques,chptr,nBlk)
end

end


# -------------------------------------
# FUNCTION DEFINITIONS
# -------------------------------------
# given v=σ^-1(i) it returns i=σ(v)
function invertOrder(sigma::Array{Int64,1})
    sigmaInv = zeros(Int64,length(sigma))
    for iii=1:length(sigma)
        sigmaInv[sigma[iii]] = iii
    end
    return sigmaInv
end

 function num_cliques(sntree::SuperNodeTree)
    return length(sntree.chptr)
end

# elimination tree algorithm from H.Liu - A Compact Row Storage Scheme for Cholesky Factors Using Elimination Trees
function etree_liu(g::Graph)
N = length(g.adjacencyList)
par = zeros(Int64,N)
ancestor = zeros(Int64,N)

elemSequence = g.reverseOrder[collect(1:N)]
for iii in elemSequence
    for vk in g.adjacencyList[iii]
        if g.ordering[vk] < g.ordering[iii]
            r = vk
            while (ancestor[r] != 0) && (ancestor[r] != iii)
                t = ancestor[r]
                ancestor[r] = iii
                r = t
            end
            if ancestor[r] == 0
                ancestor[r] = iii
                par[r] = iii
            end
        end
    end
end

return par
end




# simplified version of my own elimination tree algorithm with simplified data structure (fastest)
function etree(g::Graph)
    N = numberOfVertices(g)
    par = zeros(Int64,N)
    # loop over Vertices of graph
    for i=1:N
        value = i
        # number of i-neighbors with order higher than order of node i
        par_ = findParentDirect(g,i)
        par[i] = par_
    end
    return par
end

# perform a depth-first-search to determine the post order of the tree defined by parent and children vectors
function postOrder(par::Array{Int64,1},child::Array{Array{Int64,1}})
    N = length(par)
    order = zeros(Int64,N)
    root = findall(x->x==0,par)[1]
    stack = Array{Int64}(undef,0)
    iii = N
    push!(stack,root)
    while !isempty(stack)
        v = pop!(stack)
        order[v] = iii
        iii-=1
        push!(stack,child[v]...)
    end
    post = collect(1:N)
    sort!(post, by=x->order[x])
    return post
end

function childFromPar(par::Array{Int64,1})

    child = [Array{Int64}(undef,0) for i=1:length(par)]
    for i=1:length(par)
        par_ = par[i]
        par_ != 0 && push!(child[par_],i)
    end

    return child

end

function getSnd(sntree::SuperNodeTree,ind::Int64)
    N = length(sntree.snptr)
    if ind == N
        return sntree.snd[sntree.snptr[ind]:end]
    else
        return sntree.snd[sntree.snptr[ind]:sntree.snptr[ind+1]-1]
    end
end

function get_clique(sntree::SuperNodeTree, ind::Int64)
    N = length(sntree.chptr)
    if ind == N
        return sntree.cliques[sntree.chptr[ind]:end]
    else
        return sntree.cliques[sntree.chptr[ind]:sntree.chptr[ind + 1] - 1]
    end
end
function printCliques(sntree::SuperNodeTree)
    N = length(sntree.chptr)
    chptr = sntree.chptr
    println("Cliques of Graph:")
    for iii=1:N
         if iii != N
            clique = sntree.cliques[chptr[iii]:chptr[iii+1]-1]
        else
            clique = sntree.cliques[chptr[iii]:end]
        end
        println("$(iii): $(clique)")
    end
end

function printSupernodes(sntree::SuperNodeTree)
    N = length(sntree.snptr)
    snptr = sntree.snptr
    println("Supernodes of Graph:")
    for iii=1:N
         if iii != N
            sn = sntree.snd[snptr[iii]:snptr[iii+1]-1]
        else
            sn = sntree.snd[snptr[iii]:end]
        end
        println("$(iii): $(sn)")
    end
end


function checkDegreeCondition(v::Int64,w::Int64,degrees::Array{Int64,1})
    return degrees[v] > degrees[w] - 1
end


# Algorithm from A. Poten and C. Sun: Compact Clique Tree Data Structures in Sparse Matrix Factorizations (1989)
function pothenSun(par::Array{Int64,1},child::Array{Array{Int64,1}},post::Array{Int64,1},degrees::Array{Int64,1})
    N = length(par)
    snInd = -1*ones(Int64,N) # if snInd[v] < 0 then v is a rep vertex, otherwise v ∈ supernode[snInd[v]]
    supernode_par = -1*ones(Int64,N)

    # go through vertices in postorder
    for v in post
        child_ind = 0
        # check degree condition for all of v's childs
        for (iii,w) in enumerate(child[v])
            # if not deg+(v) > deg+(w) - 1 for a certain w, set u to be w in snd(u), add v to snd(u)
            if !checkDegreeCondition(v,w,degrees)
                snInd[w] < 0 ? (u = w) : (u = snInd[w])
                snInd[v] = u
                child_ind = iii
                break
            end
        end

        # if v is still a rep vertex (i.e. above loop didnt findall a child that fulfilled degree condition)
        if snInd[v] < 0
            u = v
        end

        for (iii,w) in enumerate(child[v])
            if iii != child_ind
                snInd[w] < 0 ? (x = w) : x = snInd[w]
                supernode_par[x] = u
            end
        end
    end

    # representative vertices
    repr = findall(x-> x < 0, snInd)
    # vertices that are the parent of representative vertices
    reprPar = supernode_par[repr]
    # take into account that all non-representative arrays are removed from the parent structure
    snpar = zeros(Int64,length(repr))

    for (iii,rp) in enumerate(reprPar)
        ind = findfirst(x->x == rp, repr)
        ind == nothing && (ind=0)
        snpar[iii] = ind
    end

    return snpar,snInd
end

function findSuperNodes(par::Array{Int64,1},child::Array{Array{Int64,1}},post::Array{Int64,1},degrees::Array{Int64,1})
    supernode_par,snInd = pothenSun(par,child,post,degrees)
    # number of vertices
    N = length(par)
    # number of representative vertices == number of supernodes
    Nrep = length(supernode_par)

    snode = zeros(Int64,N)
    snodeList = [Array{Int64}(undef,0) for i=1:N]
    snptr = zeros(Int64,Nrep)

    for iii in post
        f = snInd[iii]
        if f < 0
            push!(snodeList[iii],iii)

        else
            push!(snodeList[f],iii)
        end
    end

    kkk = 1
    jjj = 1
    for (iii,list) in enumerate(snodeList)
        len = length(list)
        if len > 0
            snptr[jjj] = kkk
            snode[kkk:kkk+len-1] = list
            kkk+= len
            jjj+=1
        end
    end
    return snode, snptr, supernode_par

end

function findCliques(g::Graph,snodes::Array{Int64,1},snptr::Array{Int64,1},supernode_par::Array{Int64,1},post::Array{Int64,1})
        postInv = invertOrder(post)

        Nc = length(supernode_par)
        cliques = Array{Int64}(undef,0)
        nBlk = zeros(Int64,Nc)
        chptr = zeros(Int64,Nc)
        jjj = 1

        for iii = 1:Nc
            if iii < Nc
                vRep = snodes[snptr[iii]:snptr[iii+1]-1][1]
            else
                vRep = snodes[snptr[iii]:end][1]
            end
            adjPlus = findHigherNeighborsSorted(g,vRep,postInv)
            deg = length(adjPlus) + 1
            cliques = [cliques;vRep;adjPlus]
            chptr[iii] = jjj
            nBlk[iii] = Base.power_by_squaring(length(adjPlus)+1, 2)
            jjj +=deg
        end

    return cliques,chptr,nBlk

end

function findParentDirect(g::Graph,v::Int64)
      order = g.ordering[v]
      neighbors = g.adjacencyList[v]
      higherOrders = filter(x-> x > order, g.ordering[neighbors])
      if length(higherOrders) > 0
        return g.reverseOrder[minimum(higherOrders)]
      else
        return 0
      end
end

function createTreeFromGraph(g::Graph)
    tree = Tree()
    N = numberOfVertices(g)
    # loop over Vertices of graph
    for i=1:N
        value = i
        # number of i-neighbors with order higher than order of node i
        higherNeighbors = findHigherNeighbors(g,i)
        degree = size(higherNeighbors,1)
        parent =findParent(g,higherNeighbors)
        order = g.ordering[i]
        node = Node([value],Int64[],degree,parent)
        push!(tree.nodes,node)
        if parent == 0
            tree.root = i
        end
    end

    # fill the children property of each node
    for node in tree.nodes
        if node.parent != 0
            push!(tree.nodes[node.parent].children,node.value_top[1])
        end
    end
    return tree

end

# Legacy code
# function createSupernodeEliminationTree(t::Tree,g::Graph)
#     superTree = Tree()
#     # go through nodes of tree in topological order
#     for nodeInd in g.reverseOrder
#         node = t.nodes[nodeInd]
#         # check if node is representative node (lowest vertex in clique)
#         child = hasLowerDegChild(node,t)
#         if child == -1
#             # if vertex is representative, i.e. doesnt have lower degree child, create new SuperNode
#             superNode = Node([nodeInd],[0],-1,-1)
#             push!(superTree.nodes,superNode)
#             node.inSuperNode = size(superTree.nodes,1)
#         else
#            # if node is not representative, add to existing supernode that contains that child
#             superNode = superTree.nodes[child.inSuperNode]
#             node.inSuperNode = child.inSuperNode
#             push!(superNode.value_top,nodeInd)

#         end
#     end
#     # determine parent / children relationship between supernodes
#     for iii=1:size(superTree.nodes,1)
#         superNode = superTree.nodes[iii]
#         highestNodeInd = superNode.value_top[indmax(g.ordering[superNode.value_top])]
#         highestNode = t.nodes[highestNodeInd]
#         if (highestNode.parent == 0)
#             superNode.parent = 0
#             superTree.root = iii
#         else
#             superNode.parent = t.nodes[highestNode.parent].inSuperNode
#         end
#     end
#     # fill the children property of each node
#     for iii=1:size(superTree.nodes,1)
#         superNode = superTree.nodes[iii]
#         if superNode.parent != 0
#             push!(superTree.nodes[superNode.parent].children,iii)
#         end
#     end

#     return superTree
# end

# # checks if node/vertex is representative (lowest degree in clique)
# function hasLowerDegChild(n::Node,t::Tree)
#     for childInd in n.children
#         child = t.nodes[childInd]
#         if !(child.degree < n.degree + 1)
#             return child
#         end
#     end
#     return -1
# end

# # FIXME: The roots
# # takes as input a SupernodeEliminationTree and turns it into a clique tree (s. Vandenberghe, Chordal Graphs and SDO, p.287)
# function createCliqueTree(t::Tree,g::Graph)
#     cliqueTree = Tree()

#     for superNode in t.nodes
#         # snd_v: the vertices of snd_v are ordered consecutively
#         snd_v = copy(superNode.value_top)
#         col_v_snd_v = Int64[]
#         for node in snd_v
#             higherNeighbors = findHigherNeighbors(g,node)
#             if size(higherNeighbors,1) > 0
#                 col_v_snd_v = union(col_v_snd_v,higherNeighbors)
#             end
#         end
#         # filter out duplicates and elements of snd(v)
#         for vertex in snd_v
#             filter!(f -> f!=vertex,col_v_snd_v)
#         end
#         sort!(col_v_snd_v, by=x->g.ordering[x])
#         node = Node(col_v_snd_v,snd_v,-1,superNode.parent,superNode.children)
#         push!(cliqueTree.nodes,node)
#     end

#     # Order the supernodes in descending order for algorithm to work
#     cliqueTree.reverseOrder = collect(1:numberOfCliques(cliqueTree))
#     cliqueTree.order = collect(numberOfCliques(cliqueTree):-1:1)

#     return cliqueTree
# end

