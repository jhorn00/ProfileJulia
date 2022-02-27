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

# Checkerboard to Path - BenchmarkTools
x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:5
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
savefig("tempSur.png")
length(x)
length(y)

# Path to Checkerboard - BenchmarkTools

x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:5
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
savefig("tempInj.png")
length(x)
length(y)


component = path_graph(ReflexiveGraph, 2)
checkerboard = box_product(component, component)
codom = add_loops(component)
checkH = homomorphism(checkerboard, codom)

################### GRIDS ###################

for n in 1:15 # number of vertices ranges from 1 to 20
    for j in 1:3 # runs each 3 times
        println(n)
        component = path_graph(ReflexiveGraph, n) # generate path graph of size n
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(component) # add loops to the codomain
        checkH = homomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***
    end
end

for n in 1:8 # number of vertices ranges from 1 to 20
    for j in 1:3 # runs each 3 times
        println(n)
        component = path_graph(ReflexiveGraph, n) # generate path graph of size n
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(checkerboard) # add loops to the codomain
        checkH = homomorphism(component, codom) # generate homomorphism ***PATH -> GRID***
    end
end

################### G larger than H for G->H ###################

large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

for i in 1:3
    homomorphism(large1, add_loops(a_sparse_five))
    homomorphism(large2, add_loops(a_sparse_three))
    homomorphism(large3, add_loops(a_sparse_seven))
    homomorphism(large4, add_loops(a_sparse_eight))
    homomorphism(large5, add_loops(large2))
    homomorphism(large6, add_loops(large3))
    homomorphism(large7, add_loops(large4))
    homomorphism(large1, add_loops(a_sparse_three))
    homomorphism(large2, add_loops(a_sparse_six))
    homomorphism(large3, add_loops(a_sparse_eight))
    homomorphism(large4, add_loops(large1))
    homomorphism(large5, add_loops(large3))
    homomorphism(a_sparse_eight, add_loops(a_sparse_seven))
    homomorphism(a_sparse_eight2, add_loops(a_sparse_six))
    homomorphism(a_sparse_five, add_loops(a_sparse_three))
    homomorphism(a_sparse_six2, add_loops(a_sparse_four))
end

################### H larger than G  for G->H ###################

homomorphism(a_sparse_three, add_loops(large1))
homomorphism(a_sparse_six, add_loops(large2))
homomorphism(a_sparse_eight, add_loops(large3))
homomorphism(a_sparse_five, add_loops(large1))
homomorphism(a_sparse_three, add_loops(large2))
homomorphism(a_sparse_seven, add_loops(large3))
homomorphism(a_sparse_eight, add_loops(large4))
show(to)

for i in 1:3
    homomorphism(a_sparse_five, add_loops(large1))
    homomorphism(a_sparse_three, add_loops(large2))
    homomorphism(a_sparse_seven, add_loops(large3))
    homomorphism(a_sparse_eight, add_loops(large4))
    homomorphism(large2, add_loops(large5))
    homomorphism(large3, add_loops(large6))
    homomorphism(large4, add_loops(large7))
    homomorphism(a_sparse_three, add_loops(large1))
    homomorphism(a_sparse_six, add_loops(large2))
    homomorphism(a_sparse_eight, add_loops(large3))
    homomorphism(large1, add_loops(large4))
    homomorphism(large3, add_loops(large5))
    homomorphism(a_sparse_seven, add_loops(a_sparse_eight))
    homomorphism(a_sparse_six, add_loops(a_sparse_eight2))
    homomorphism(a_sparse_three, add_loops(a_sparse_five))
    homomorphism(a_sparse_four, add_loops(a_sparse_six2))
end

# G about the same size as H

for i in 1:3
    # same
    homomorphism(a_sparse_five, add_loops(a_sparse_five))
    homomorphism(a_sparse_eight, add_loops(a_sparse_eight))
    homomorphism(a_sparse_seven, add_loops(a_sparse_eight2))
    homomorphism(a_sparse_eight, add_loops(a_sparse_seven))
    homomorphism(a_sparse_three, add_loops(a_sparse_four))
    homomorphism(a_sparse_six, add_loops(a_sparse_five))
    homomorphism(a_sparse_four, add_loops(a_sparse_five))
    homomorphism(a_sparse_five, add_loops(a_sparse_four))
    homomorphism(a_sparse_four, add_loops(a_sparse_three))
    homomorphism(a_sparse_seven, add_loops(a_sparse_eight))
    homomorphism(a_sparse_six, add_loops(a_sparse_six2))
    homomorphism(a_sparse_six2, add_loops(a_sparse_five))
    homomorphism(a_sparse_five, add_loops(a_sparse_six2))
end