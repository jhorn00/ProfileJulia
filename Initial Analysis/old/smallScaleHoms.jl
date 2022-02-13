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

#small
#injective
# The one below this takes super long despite being smaller for homomorphims.
# I'm not sure if it is just that much harder to calculate or if it is a bug.
# Could just be the calcultions, since I think I saw some other injective homs
# take a bit longer than their surjective counterparts.
#sparse_injection = homomorphisms(sparse_from, co_sparse_to)

#=
small_sparse_inj = @benchmark homomorphism(sparse_from, co_sparse_to)
small_sparse_inj2 = @benchmark homomorphism(sparse_from2, co_sparse_to2)
=#

#surjective
#=
small_sparse_sur = @benchmark homomorphism(sparse_to, co_sparse_from)
small_sparse_sur2 = @benchmark homomorphism(sparse_to2, co_sparse_from2)
=#

#large
#injection
#=
sparse_injection = homomorphism(sparse_from, co_sparse_to)
large_sparse_inj = @benchmark homomorphism(sparse_from, co_sparse_to)
large_sparse_inj2 = @benchmark homomorphism(sparse_from2, co_sparse_to2)
=#

#surjection
#=
sparse_surjection = homomorphism(sparse_from, co_sparse_to)
large_sparse_sur = @benchmark homomorphism(sparse_to, co_sparse_from)
large_sparse_sur2 = @benchmark homomorphism(sparse_to2, co_sparse_from2)
=#

#ratios
ratio(median(small_sparse_inj), median(small_sparse_sur))
ratio(median(large_sparse_inj), median(large_sparse_sur))
# calculate the growth^^^^^ dont be lazy
ratio(median(small_sparse_inj), median(large_sparse_inj))
ratio(median(small_sparse_sur), median(large_sparse_sur))

#larger
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