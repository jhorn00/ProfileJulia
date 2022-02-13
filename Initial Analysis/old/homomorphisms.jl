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
        print("Graph pair $i:   ")
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

# This checks every possible pair. Injection/Surjection isn't an accurate description for most
# pairs, but the data is still useful.
function autoPlotAll(fromList, toList)
    println("Autoplotting Homs...\nTotal pairs: $(length(toList) * length(toList))")
    x1 = Int64[]
    y1 = Float64[]
    x2 = Int64[]
    y2 = Float64[]
    x3 = Int64[]
    x4 = Int64[]
    count = 1
    for i in 1:length(fromList)
        f = fromList[i]
        for j in 1:length(toList)
            print("Graph pair $count:   ")
            t = toList[j]
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
            count = count + 1
        end
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

sparse_from_base3 = sparse_from3 = @acset Graphs.Graph begin
    V = 2
    E = 1
    src = [1]
    tgt = [2]
end
draw(sparse_from3)

sparse_to_base3 = sparse_to3 = @acset Graphs.Graph begin
    V = 4
    E = 3
    src = [1, 2, 3]
    tgt = [2, 3, 4]
end
draw(sparse_to3)

sparse_from_base4 = sparse_from4 = @acset Graphs.Graph begin
    V = 5
    E = 5
    src = [1, 1, 2, 3, 4]
    tgt = [3, 5, 5, 5, 5]
end
draw(sparse_from4)

sparse_to_base4 = sparse_to4 = @acset Graphs.Graph begin
    V = 7
    E = 7
    src = [1, 3, 4, 5, 6, 6, 7]
    tgt = [4, 1, 2, 3, 3, 4, 2]
end
draw(sparse_to4)

# Notably, all of the above are acyclic

# Small Graph Formation
co_sparse_from = add_loops(sparse_from)
co_sparse_to = add_loops(sparse_to)

co_sparse_from2 = add_loops(sparse_from2)
co_sparse_to2 = add_loops(sparse_to2)

co_sparse_from3 = add_loops(sparse_from3)
co_sparse_to3 = add_loops(sparse_to3)

co_sparse_from4 = add_loops(sparse_from4)
co_sparse_to4 = add_loops(sparse_to4)

# Large Graph Formation
sparse_from_large = sparse_from = apex(product(sparse_from, sparse_from))
co_sparse_from = add_loops(sparse_from)
sparse_to_large = sparse_to = apex(product(sparse_to, sparse_to))
co_sparse_to = add_loops(sparse_to)

sparse_from_large2 = sparse_from2 = apex(product(sparse_from2, sparse_from2))
co_sparse_from2 = add_loops(sparse_from2)
sparse_to_large2 = sparse_to2 = apex(product(sparse_to2, sparse_to2))
co_sparse_to2 = add_loops(sparse_to2)

sparse_from_large3 = sparse_from3 = apex(product(sparse_from3, sparse_from3))
co_sparse_from3 = add_loops(sparse_from3)
sparse_to_large3 = sparse_to3 = apex(product(sparse_to3, sparse_to3))
co_sparse_to3 = add_loops(sparse_to3)

sparse_from_large4 = sparse_from4 = apex(product(sparse_from4, sparse_from4))
co_sparse_from4 = add_loops(sparse_from4)
sparse_to_large4 = sparse_to4 = apex(product(sparse_to4, sparse_to4))
co_sparse_to4 = add_loops(sparse_to4)
# Larger Graph Testing
sparse_from_larger = sparse_from = apex(product(sparse_from, sparse_from_base))
co_sparse_from = add_loops(sparse_from)
sparse_to_larger = sparse_to = apex(product(sparse_to, sparse_to_base))
co_sparse_to = add_loops(sparse_to)

sparse_from_larger2 = sparse_from2 = apex(product(sparse_from2, sparse_from_base2))
co_sparse_from2 = add_loops(sparse_from2)
sparse_to_larger2 = sparse_to2 = apex(product(sparse_to2, sparse_to_base2))
co_sparse_to2 = add_loops(sparse_to2)

sparse_from_larger3 = sparse_from3 = apex(product(sparse_from3, sparse_from_base3))
co_sparse_from3 = add_loops(sparse_from3)
sparse_to_larger3 = sparse_to3 = apex(product(sparse_to3, sparse_to_base3))
co_sparse_to3 = add_loops(sparse_to3)

sparse_from_larger4 = sparse_from4 = apex(product(sparse_from4, sparse_from_base4))
co_sparse_from4 = add_loops(sparse_from4)
sparse_to_larger4 = sparse_to4 = apex(product(sparse_to4, sparse_to_base4))
co_sparse_to4 = add_loops(sparse_to4)

#autoPlot
# copy/paste helper:
# sparse_from_base, sparse_from_large, sparse_from_larger
# sparse_to_base, sparse_to_large, sparse_to_larger
fromList = [sparse_from_base, sparse_from_base2, sparse_from_large, sparse_from_large2, sparse_from_larger, sparse_from_larger2, sparse_from_base3, sparse_from_large3, sparse_from_larger3, sparse_from_base4, sparse_from_large4, sparse_from_larger4]
toList = [sparse_to_base, sparse_to_base2, sparse_to_large, sparse_to_large2, sparse_to_larger, sparse_to_larger2, sparse_to_base3, sparse_to_large3, sparse_to_larger3, sparse_to_base4, sparse_to_large4, sparse_to_larger4]

# autoPlot(fromList, toList)
# comment out so it isn't run accidentally
# autoPlotAll(fromList, toList)






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
