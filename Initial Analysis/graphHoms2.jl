using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
using TimerOutputs
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
include("autoplot.jl")
include("graph_bank.jl")

################################### Run the above code ###################################

# function homomorphism_query(X::StructACSet{S}; count::Bool = false) where {S}
#     offsets = cumsum([0; [nparts(X, c) for c in ob(S)]])
#     nelems = offsets[end]

#     diagram = HomomorphismQueryDiagram{Symbol}()
#     params = Pair[]
#     add_parts!(diagram, :Junction, nelems)
#     if !count
#         add_parts!(diagram, :OuterPort, nelems, outer_junction = 1:nelems)
#     end
#     for (i, c) in enumerate(ob(S))
#         n = nparts(X, c)
#         boxes = add_parts!(diagram, :Box, n, name = c)
#         add_parts!(diagram, :Port, n, box = boxes, port_name = :_id,
#             junction = (1:n) .+ offsets[i])
#     end
#     for (f, c, i, j) in zip(hom(S), dom(S), dom_nums(S), codom_nums(S))
#         n = nparts(X, c)
#         add_parts!(diagram, :Port, n, box = (1:n) .+ offsets[i], port_name = f,
#             junction = X[:, f] .+ offsets[j])
#     end
#     for (f, c, i) in zip(attr(S), adom(S), adom_nums(S))
#         n = nparts(X, c)
#         junctions = add_parts!(diagram, :Junction, n)
#         add_parts!(diagram, :Port, n, box = (1:n) .+ offsets[i], port_name = f,
#             junction = junctions)
#         append!(params, Iterators.map(Pair, junctions, X[:, f]))
#     end
#     (diagram, params)
# end

# Targeted functions
# function homomorphism(X::ACSet, Y::ACSet, ::HomomorphismQuery)
#     columns = query(Y, homomorphism_query(X)...; table_type = AbstractVector)
#     isempty(first(columns)) ? nothing :
#     make_homomorphism(map(first, columns), X, Y)
# end



# timers to profile functions
# const to = TimerOutput()


homomorphism(X::ACSet, Y::ACSet; alg = BacktrackingSearch(), kw...) =
    homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
    result = nothing
    backtracking_search(X, Y; kw...) do α
        result = α
        return true
    end
    result
end





h = length(homomorphisms(line_four, directional_2x2))
h1 = homomorphism(line_four, directional_2x2, 5)

print(h)