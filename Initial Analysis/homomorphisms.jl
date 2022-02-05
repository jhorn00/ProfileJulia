using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
draw(g) = to_graphviz(g, node_labels = true, edge_labels = true)
GraphvizGraphs.to_graphviz(f::ACSetTransformation; kw...) =
    to_graphviz(GraphvizGraphs.to_graphviz_property_graph(f; kw...))

function GraphvizGraphs.to_graphviz_property_graph(f::ACSetTransformation; kw...)
    pg = GraphvizGraphs.to_graphviz_property_graph(dom(f); kw...)
    vcolors = hex.(range(colorant"#0021A5", stop = colorant"#FA4616", length = nparts(codom(f), :V)))
    ecolors = hex.(range(colorant"#6C9AC3", stop = colorant"#E28F41", length = nparts(codom(f), :E)))
    hex.(colormap("Oranges", nparts(codom(f), :V)))
    for v in vertices(dom(f))
        fv = f[:V](v)
        set_vprops!(pg, v, Dict(:color => "#$(vcolors[fv])"))
    end
    for e in edges(dom(f))
        fe = f[:E](e)
        set_eprops!(pg, e, Dict(:color => "#$(ecolors[fe])"))
    end
    pg
end

add_loops!(g) = add_parts!(g, :E, nparts(g, :V), src = parts(g, :V), tgt = parts(g, :V))
add_loops(g) = begin
    h = copy(g)
    add_loops!(h)
    return h
end

################################### Run the above code ###################################

# This will allow a better look at the breakdown of individual functions
#using TimerOutputs
#tmr = TimerOutput()

# TODO
#import function/method and extend them
#scalability
#UndirectedWiringDiagram - number of boxes and number of wires/junction
#partitiion the negihbors of every vertex
#bipartite graph and partition the neighborhoods into ports - each port gets a subset of the negihbors





# Quick n' dirty mapping helper
function mappings(homomorphism)
    V = collect(homomorphism[:V])
    E = collect(homomorphism[:E])
    for i in 1:length(V)
        println("$(V[i]) maps to $(E[i])")
    end
end

# Sparse Graph
sparse_from_base = sparse_from = @acset Graphs.Graph begin
    V = 4
    E = 4
    src = [1, 1, 2, 3]
    tgt = [2, 3, 4, 4]
end
draw(sparse_from)

sparse_to_base = sparse_to = @acset Graphs.Graph begin
    V = 8
    E = 8
    src = [1, 2, 2, 3, 4, 6, 7, 8]
    tgt = [2, 3, 5, 7, 2, 4, 8, 5]
end
draw(sparse_to)

co_sparse_from = add_loops(sparse_from)
co_sparse_to = add_loops(sparse_to)

# Small Graph Testing
#injective?
# The one below this takes super long despite being smaller for homomorphims.
# I'm not sure if it is just that much harder to calculate or if it is a bug.
# Could just be the calcultions, since I think I saw some other injective homs
# take a bit longer than their surjective counterparts.
#sparse_injection = homomorphisms(sparse_from, co_sparse_to)
small_sparse_inj1 = @benchmark homomorphism(sparse_from, co_sparse_to)

#surjective?
#sparse_surjection = homomorphisms(sparse_to, co_sparse_from)
small_sparse_inj2 = @benchmark homomorphism(sparse_to, co_sparse_from)

# Large Graph Testing
sparse_from = apex(product(sparse_from, sparse_from))
co_sparse_from = add_loops(sparse_from)
sparse_to = apex(product(sparse_to, sparse_to))
co_sparse_to = add_loops(sparse_to)

#injection
sparse_injection = homomorphism(sparse_from, co_sparse_to)
large_sparse_inj1 = @benchmark homomorphism(sparse_from, co_sparse_to)

#surjection
sparse_surjection = homomorphism(sparse_from, co_sparse_to)
large_sparse_inj2 = @benchmark homomorphism(sparse_to, co_sparse_from)

ratio(median(small_sparse_inj1), median(small_sparse_inj2))
ratio(median(large_sparse_inj1), median(large_sparse_inj2))
# calculate the growth^^^^^ dont be lazy
ratio(median(small_sparse_inj1), median(large_sparse_inj1))
ratio(median(small_sparse_inj2), median(large_sparse_inj2))

# Larger Graph Testing
sparse_from = apex(product(sparse_from, sparse_from_base))
co_sparse_from = add_loops(sparse_from)
sparse_to = apex(product(sparse_to, sparse_to_base))
co_sparse_to = add_loops(sparse_to)

#injection
sparse_injection = homomorphism(sparse_from, co_sparse_to)
larger_sparse_inj1 = @benchmark homomorphism(sparse_from, co_sparse_to)

#surjection
sparse_surjection = homomorphism(sparse_from, co_sparse_to)
larger_sparse_inj2 = @benchmark homomorphism(sparse_to, co_sparse_from)

ratio(median(larger_sparse_inj1), median(larger_sparse_inj2))
# calculate the growth^^^^^ dont be lazy
ratio(median(large_sparse_inj1), median(larger_sparse_inj1))
ratio(median(large_sparse_inj2), median(larger_sparse_inj2))

# growth - plot this, don't be lazy
median(small_sparse_inj1)
median(small_sparse_inj2)
median(large_sparse_inj1)
median(large_sparse_inj2)
median(larger_sparse_inj1)
median(larger_sparse_inj2)

# Dense Graph


# Average-ish Graph

t = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 2, 1]
    tgt = [2, 3, 3]
end
draw(t)

T = @acset Graphs.Graph begin
    V = 6
    E = 9
    src = [1, 2, 1, 3, 1, 5, 2, 2, 4]
    tgt = [2, 3, 3, 4, 4, 6, 5, 6, 6]
end
draw(T)


# Disjoint (disconnected?) Graph - sparse, dense, avg???






# get the homomorphims
thoms = homomorphisms(t, add_loops(T))
# this is one of the tivial homomorphims
draw(thoms[27])
thoms[27]

draw(t)
tt = apex(product(t, add_loops(t)))
draw(tt)
ttt = apex(product(tt, add_loops(tt)))
draw(ttt)
