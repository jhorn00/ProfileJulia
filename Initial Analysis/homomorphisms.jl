using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
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



# Auto Calculation and Plotting
# give a list of to and from graphs -> tests and plots them based on vertex/edge amounts
function autoPlot(fromList, toList)
    if length(fromList) != length(toList)
        println("From and to lists should be the same size.")
        return
    end
    println("Autoplotting Homs...\nTotal pairs: $(length(toList))")
    x1 = Int64[]
    y1 = Float64[]
    x2 = Int64[]
    y2 = Float64[]
    x3 = Int64[]
    x4 = Int64[]
    for i in 1:length(fromList)
        print("Graph pair $i: ")
        f = fromList[i]
        t = toList[i]
        #injection
        append!(y1, time(median(@benchmark homomorphism($f, add_loops($t)))))
        append!(x1, length(vertices(f)))
        append!(x3, length(edges(t)))
        print("Injection complete.   ")
        #surjection
        append!(y2, time(median(@benchmark homomorphism($t, add_loops($f)))))
        append!(x2, length(vertices(t)))
        append!(x4, length(edges(t)))
        print("Surjection complete.\n")
    end
    scatter([x1, x2], [y1, y2], title = "Autoplotted Graph Vertices", xlabel = "Number of \"From\" Vertices", ylabel = "Single Hom Calculation Time (ns)", label = ["Injective" "Surjective"])
    savefig("autoVertex.png")
    scatter([x3, x4], [y1, y2], title = "Autoplotted Graph Edges", xlabel = "Number of Edges", ylabel = "Single Hom Calculation Time (ns)", label = ["Injective" "Surjective"])
    savefig("autoEdge.png")
end

#potentially make another version that maps each from to each to - would probably take a long time to run



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

sparse_from_base2 = sparse_from2 = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 1, 2]
    tgt = [2, 3, 3]
end
draw(sparse_from2)

sparse_to_base2 = sparse_to2 = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [1, 2, 3, 5, 6, 6]
    tgt = [2, 3, 5, 4, 3, 5]
end
draw(sparse_to2)

co_sparse_from = add_loops(sparse_from)
co_sparse_to = add_loops(sparse_to)
co_sparse_from2 = add_loops(sparse_from2)
co_sparse_to2 = add_loops(sparse_to2)


# Small Graph Testing
#injective
# The one below this takes super long despite being smaller for homomorphims.
# I'm not sure if it is just that much harder to calculate or if it is a bug.
# Could just be the calcultions, since I think I saw some other injective homs
# take a bit longer than their surjective counterparts.
#sparse_injection = homomorphisms(sparse_from, co_sparse_to)
small_sparse_inj = @benchmark homomorphism(sparse_from, co_sparse_to)
small_sparse_inj2 = @benchmark homomorphism(sparse_from2, co_sparse_to2)


#surjective
#sparse_surjection = homomorphisms(sparse_to, co_sparse_from)
small_sparse_sur = @benchmark homomorphism(sparse_to, co_sparse_from)
small_sparse_sur2 = @benchmark homomorphism(sparse_to2, co_sparse_from2)

# Large Graph Testing
sparse_from_large = sparse_from = apex(product(sparse_from, sparse_from))
co_sparse_from = add_loops(sparse_from)
sparse_to_large = sparse_to = apex(product(sparse_to, sparse_to))
co_sparse_to = add_loops(sparse_to)

sparse_from_large2 = sparse_from2 = apex(product(sparse_from2, sparse_from2))
co_sparse_from2 = add_loops(sparse_from2)
sparse_to_large2 = sparse_to2 = apex(product(sparse_to2, sparse_to2))
co_sparse_to2 = add_loops(sparse_to2)

#injection
sparse_injection = homomorphism(sparse_from, co_sparse_to)
large_sparse_inj = @benchmark homomorphism(sparse_from, co_sparse_to)

large_sparse_inj2 = @benchmark homomorphism(sparse_from2, co_sparse_to2)

#surjection
sparse_surjection = homomorphism(sparse_from, co_sparse_to)
large_sparse_sur = @benchmark homomorphism(sparse_to, co_sparse_from)

large_sparse_sur2 = @benchmark homomorphism(sparse_to2, co_sparse_from2)

ratio(median(small_sparse_inj), median(small_sparse_sur))
ratio(median(large_sparse_inj), median(large_sparse_sur))
# calculate the growth^^^^^ dont be lazy
ratio(median(small_sparse_inj), median(large_sparse_inj))
ratio(median(small_sparse_sur), median(large_sparse_sur))

# Larger Graph Testing
sparse_from_larger = sparse_from = apex(product(sparse_from, sparse_from_base))
co_sparse_from = add_loops(sparse_from)
sparse_to_larger = sparse_to = apex(product(sparse_to, sparse_to_base))
co_sparse_to = add_loops(sparse_to)

sparse_from_larger2 = sparse_from2 = apex(product(sparse_from2, sparse_from_base2))
co_sparse_from2 = add_loops(sparse_from2)
sparse_to_larger2 = sparse_to2 = apex(product(sparse_to2, sparse_to_base2))
co_sparse_to2 = add_loops(sparse_to2)

#injection
sparse_injection = homomorphism(sparse_from, co_sparse_to)
larger_sparse_inj = @benchmark homomorphism(sparse_from, co_sparse_to)

larger_sparse_inj2 = @benchmark homomorphism(sparse_from2, co_sparse_to2)

#surjection
sparse_surjection = homomorphism(sparse_from, co_sparse_to)
larger_sparse_sur = @benchmark homomorphism(sparse_to, co_sparse_from)

larger_sparse_sur2 = @benchmark homomorphism(sparse_to2, co_sparse_from2)

ratio(median(larger_sparse_inj), median(larger_sparse_sur))
# calculate the growth^^^^^ dont be lazy
ratio(median(large_sparse_inj), median(larger_sparse_inj))
ratio(median(large_sparse_sur), median(larger_sparse_sur))

# Sparse Plots - Vertices
x1 = [length(vertices(sparse_from_base)), length(vertices(sparse_from_large)), length(vertices(sparse_from_larger)), length(vertices(sparse_from_base2)), length(vertices(sparse_from_large2)), length(vertices(sparse_from_larger2))]
y1 = [time(median(small_sparse_inj)), time(median(large_sparse_inj)), time(median(larger_sparse_inj)), time(median(small_sparse_inj2)), time(median(large_sparse_inj2)), time(median(larger_sparse_inj2))] # should be in nanoseconds
x2 = [length(vertices(sparse_to_base)), length(vertices(sparse_to_large)), length(vertices(sparse_to_larger)), length(vertices(sparse_to_base2)), length(vertices(sparse_to_large2)), length(vertices(sparse_to_larger2))]
y2 = [time(median(small_sparse_sur)), time(median(large_sparse_sur)), time(median(larger_sparse_sur)), time(median(small_sparse_sur2)), time(median(large_sparse_sur2)), time(median(larger_sparse_sur2))]
scatter([x1, x2], [y1, y2], title = "Sparse Graph Vertices", xlabel = "Number of \"From\" Vertices", ylabel = "Single Hom Calculation Time (ns)", label = ["Injective" "Surjective"])
savefig("vertex_inj_sur_homs.png")

# Sparse Plots - Edges <-- Will be similar to the vertices given the nature of sparse graphs.
x1 = [length(edges(sparse_from_base)), length(edges(sparse_from_large)), length(edges(sparse_from_larger))]
y1 = [time(median(small_sparse_inj)), time(median(large_sparse_inj)), time(median(larger_sparse_inj))] # should be in nanoseconds
x2 = [length(edges(sparse_to_base)), length(edges(sparse_to_large)), length(edges(sparse_to_larger))]
y2 = [time(median(small_sparse_sur)), time(median(large_sparse_sur)), time(median(larger_sparse_sur))]
scatter([x1, x2], [y1, y2], title = "Sparse Graph Edges", xlabel = "Number of Edges", ylabel = "Single Hom Calculation Time (ns)", label = ["Injective" "Surjective"])
savefig("edge_inj_sur_homs.png")

#autoPlot
fromList = [sparse_from_base, sparse_from_base2, sparse_from_large, sparse_from_large2, sparse_from_larger, sparse_from_larger2]
toList = [sparse_to_base, sparse_to_base2, sparse_to_large, sparse_to_large2, sparse_to_larger, sparse_to_larger2]
autoPlot(fromList, toList)







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
