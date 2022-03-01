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

################################### Run the above code ###################################

include("autoplot.jl")
include("graph_bank.jl")

fromList = [a_sparse_from, a_sparse_from2, a_sparse_from3, a_sparse_from4, a_sparse_from5, a_complete_from]
toList = [a_sparse_to, a_sparse_to2, a_sparse_to3, a_sparse_to4, a_sparse_to5, a_complete_to]
#autoGen(fromList, 1000, 1000)
#autoGen(toList, 1000, 1000)


# autoGens() Demonstration: It takes two lists of the same size and
# appends expanded graphs to them such that they will remain the same size.
# It returns nothing.
#autoGens(fromList, toList, 500, 500)
#autoShuffle(fromList, toList, 1500, 1500)
#autoShuffle(fromList, toList, 500, 500)
#autoShuffle(fromList, toList, 500, 500)
#lightShuffle(fromList, toList, 500, 500, 10)
#lightShuffle(fromList, toList, 500, 500, 10)
#lightShuffle(fromList, toList, 500, 500, 10)
#autoGens(fromList, toList, 500, 500)
#lightShuffle(fromList, toList, 500, 500, 10)
autoGens(fromList, toList, 300, 300)
autoGens(fromList, toList, 300, 300)
for i in 1:2
    autoShuffle(fromList, toList, 300, 300)
end
length(fromList)
length(toList)

for i in 1:length(fromList)
    println(length(edges(fromList[i])))
end

# autoPlot(fromList, toList)
quickPlot(fromList, toList)