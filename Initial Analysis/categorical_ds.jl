using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs

# The initial test case here will involve a simple directed graph 1 -> 2

# Traditional Julia graph generation
# simple edgelist
struct EdgeList
    vertices::Int
    edges::Int
    src::Vector{Int}
    tgt::Vector{Int}
end

# edgelist instantiation
g1 = @benchmark EdgeList(2, 1, [1], [2])

# simple adjacencylist
struct AdjacencyList
    vertices::Int
    edges::Int
    src_index::Vector{Vector{Int}}
    tgt_index::Vector{Vector{Int}}
end

# adjacencylist instantiation
g2 = @benchmark AdjacencyList(2, 1, [[1], []], [[], [1]])

# The adjacencylist takes 10 times as long to instantiate with identical data, and consumes ~7 times the memory.
ratio(median(g2), median(g1))

# Catlab acset graph representation
g3 = @benchmark @acset Graphs.Graph begin
    V = 2
    E = 1
    src = [1]
    tgt = [2]
end

# Comparing acset graph with the edgelist graph
ratio(median(g3), median(g1))
# The acset implementation is ~185 times slower to instantiate, which meets expectations.
# The acset functionality far exceeds that of the edgelist.

# Comparing acset graph with adjacencylist graph
ratio(median(g3), median(g2))
# This information is not new. We knew that adjacencylist was slower than edgelist to instantiate.

# First we should compare this with more complex graphs. Following that we will take a look at how Catlab compares to naive
# graph functions.


# This is a classic 4-member graph (what does it model again? equivalent functions but I can't remember the name)
h1 = @benchmark EdgeList(4, 5, [1, 1, 1, 2, 3], [2, 3, 4, 4, 4])
# remember the vectors hold the list of edges with the source or target of vertex i
h2 = @benchmark AdjacencyList(4, 5, [[1, 2, 3], [4], [5], []], [[], [1], [2], [3, 4, 5]])
# finally the acset graph - I would like to note here that the following notation is far more intuitive to construct
# it also has errors to notify you if your schema and data are inconsistent
h3 = @benchmark @acset Graphs.Graph begin
    V = 4
    E = 5
    src = [1, 1, 1, 2, 3]
    tgt = [2, 3, 4, 4, 4]
end
ratio(median(h3), median(h1))
ratio(median(h3), median(h2))
# This gives me ideas to explore what exactly influences the instantiation time increases.
# The graph functions are more likely to show areas where we can find improvements made by Catlab.

# Commutative square graph:
j1 = @benchmark EdgeList(6, 9, [1, 1, 1, 2, 3, 3, 3, 4, 5], [2, 3, 4, 4, 4, 5, 6, 6, 6])
j2 = @benchmark AdjacencyList(6, 9, [[1, 2, 3], [4], [5, 6, 7], [8], [9], []], [[], [1], [2], [3, 4, 5], [6], [7, 8, 9]])
j3 = @benchmark @acset Graphs.Graph begin
    V = 6
    E = 9
    src = [1, 1, 1, 2, 3, 3, 3, 4, 5]
    tgt = [2, 3, 4, 4, 4, 5, 6, 6, 6]
end
ratio(median(j3), median(j1))
ratio(median(j3), median(j2))
# the above seems to present a minimal change in instantiation performance

# Functions:
# Homs
# What else?

from = @acset Graphs.Graph begin
    V = 4
    E = 5
    src = [1, 1, 1, 2, 3]
    tgt = [2, 3, 4, 4, 4]
end

to = @acset Graphs.Graph begin
    V = 6
    E = 9
    src = [1, 1, 1, 2, 3, 3, 3, 4, 5]
    tgt = [2, 3, 4, 4, 4, 5, 6, 6, 6]
end

length(homomorphisms(from, to))

# Edge list
e1 = EdgeList(4, 5, [1, 1, 1, 2, 3], [2, 3, 4, 4, 4])
e2 = EdgeList(6, 9, [1, 1, 1, 2, 3, 3, 3, 4, 5], [2, 3, 4, 4, 4, 5, 6, 6, 6])
function naiveHomCount(from, to)
    # cases where they all map to the same vertex
    sum = to.vertices
    for i in 1:from.vertices
        
    end
end

naiveHomCount(e1, e2)