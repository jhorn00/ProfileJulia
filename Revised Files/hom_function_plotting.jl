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
include("graph_bank.jl")
include("autoplot.jl")

################################### Run the above code ###################################
numSamples = 500
BenchmarkTools.DEFAULT_PARAMETERS.samples = numSamples

# Checkerboard surjection - BenchmarkTools
x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:3
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(component)
        checkH = @benchmark homomorphism($checkerboard, $codom)
        for_x = Array{Int64,1}(undef, length(checkH.times))
        fill!(for_x, n)
        append!(x, for_x)
        append!(y, checkH.times)
    end
end
scatter([x], [y], title = "Homomorphism Function", xlabel = "Graph Dimensions (Path Graph Vertex count)", ylabel = "Single Hom Calculation Time (ns)")
savefig("checkerSur.png")
length(x)
length(y)

# Checkerboard injection - BenchmarkTools
x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:3
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(checkerboard)
        checkH = @benchmark homomorphism($component, $codom)
        for_x = Array{Int64,1}(undef, length(checkH.times))
        fill!(for_x, n)
        append!(x, for_x)
        append!(y, checkH.times)
    end
end
scatter([x], [y], title = "Homomorphism Function", xlabel = "Graph Dimensions (Path Graph Vertex count)", ylabel = "Single Hom Calculation Time (ns)")
savefig("checkerInj.png")
length(x)
length(y)


