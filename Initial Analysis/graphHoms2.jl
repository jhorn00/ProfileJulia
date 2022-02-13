using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.CSets
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





# function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
#     monic=false, iso=false, initial=(;)) where {Ob, S<:SchemaDescType{Ob}}
# # Fail early if no monic/isos exist on cardinality grounds.
# if iso isa Bool
# iso = iso ? Ob : ()
# end
# for c in iso
# nparts(X,c) == nparts(Y,c) || return false
# end
# if monic isa Bool
# monic = monic ? Ob : ()
# end
# # Injections between finite sets are bijections, so reduce to that case.
# monic = unique([iso..., monic...])
# for c in monic
# nparts(X,c) <= nparts(Y,c) || return false
# end

# # Initialize state variables for search.
# assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
# assignment_depth = map(copy, assignment)
# inv_assignment = NamedTuple{Ob}(
# (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
# state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)

# # Make any initial assignments, failing immediately if inconsistent.
# for (c, c_assignments) in pairs(initial)
# for (x, y) in partial_assignments(c_assignments)
# assign_elem!(state, 0, Val{c}, x, y) || return false
# end
# end

# # Start the main recursion for backtracking search.
# backtracking_search(f, state, 1)
# end

# function backtracking_search(f, state::BacktrackingState, depth::Int)
# # Choose the next unassigned element.
# mrv, mrv_elem = find_mrv_elem(state, depth)
# if isnothing(mrv_elem)
# # No unassigned elements remain, so we have a complete assignment.
# return f(ACSetTransformation(state.assignment, state.dom, state.codom))
# elseif mrv == 0
# # An element has no allowable assignment, so we must backtrack.
# return false
# end
# c, x = mrv_elem

# # Attempt all assignments of the chosen element.
# Y = state.codom
# for y in parts(Y, c)
# assign_elem!(state, depth, Val{c}, x, y) &&
# backtracking_search(f, state, depth + 1) &&
# return true
# unassign_elem!(state, depth, Val{c}, x)
# end
# return false
# end



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



h1 = homomorphism(line_four, directional_2x2)
