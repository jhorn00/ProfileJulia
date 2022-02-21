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
include("graph_bank.jl")
include("autoplot.jl")

# homomorphisms imports
import Catlab.CategoricalAlgebra.CSets: homomorphisms, homomorphism
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components

# backtracking_search imports
import Catlab.Theories: SchemaDescType
import Catlab.CategoricalAlgebra.CSets: BacktrackingState
import Catlab.CategoricalAlgebra.CSets: find_mrv_elem, assign_elem!, unassign_elem!

numSamples = 500
BenchmarkTools.DEFAULT_PARAMETERS.samples = numSamples

################################### Run the above code ###################################

const to = TimerOutput()

# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    result = nothing
    @timeit to "homomorphisms() call" homomorphisms(X, Y; kw...) do α
        result = α
        return true
    end
    result
end


# it uses two homomorphisms functions
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S}; kw...) where {S}
    results = ACSetTransformation{S}[]
    @timeit to "recursive homomorphisms() call" homomorphisms(X, Y; kw...) do α
        push!(results, map_components(deepcopy, α))
        return false
    end
    results
end
homomorphisms(f, X::StructACSet, Y::StructACSet; monic = false, iso = false, initial = (;)) = @timeit to "backtracking() call" backtracking_search(f, X, Y, monic = monic, iso = iso, initial = initial)

# Backtracking
# function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
#     monic = false, iso = false, initial = (;)) where {Ob,S<:SchemaDescType{Ob}}
#     # Fail early if no monic/isos exist on cardinality grounds.
#     if iso isa Bool
#         iso = iso ? Ob : ()
#     end
#     @timeit to "for c in iso" for c in iso
#         nparts(X, c) == nparts(Y, c) || return false
#     end

#     if monic isa Bool
#         monic = monic ? Ob : ()
#     end
#     # Injections between finite sets are bijections, so reduce to that case.
#     @timeit to "unique() call" monic = unique([iso..., monic...])
#     @timeit to "for c in iso" for c in monic
#         nparts(X, c) <= nparts(Y, c) || return false
#     end
#     # Initialize state variables for search.
#     @timeit to "assignment" assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
#     @timeit to "assignment_depth" assignment_depth = map(copy, assignment)
#     @timeit to "inv_assignment" inv_assignment = NamedTuple{Ob}(
#         (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
#     @timeit to "BacktrackingState" state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)
#     # Make any initial assignments, failing immediately if inconsistent.
#     @timeit to "for (c, c_assignments) in pairs" for (c, c_assignments) in pairs(initial)
#         @timeit to "for(x, y) in partial_assignments" for (x, y) in partial_assignments(c_assignments)
#             assign_elem!(state, 0, Val{c}, x, y) || return false
#         end
#     end
#     # Start the main recursion for backtracking search.
#     @timeit to "Start backtrack recursion" backtracking_search(f, state, 1)
# end

function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
    monic = false, iso = false, initial = (;)) where {Ob,S<:SchemaDescType{Ob}}
    # Fail early if no monic/isos exist on cardinality grounds.
    if iso isa Bool
        iso = iso ? Ob : ()
    end
    for c in iso
        nparts(X, c) == nparts(Y, c) || return false
    end

    if monic isa Bool
        monic = monic ? Ob : ()
    end
    # Injections between finite sets are bijections, so reduce to that case.
    monic = unique([iso..., monic...])
    for c in monic
        nparts(X, c) <= nparts(Y, c) || return false
    end
    # Initialize state variables for search.
    assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
    assignment_depth = map(copy, assignment)
    inv_assignment = NamedTuple{Ob}(
        (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
    state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)
    # Make any initial assignments, failing immediately if inconsistent.
    for (c, c_assignments) in pairs(initial)
        for (x, y) in partial_assignments(c_assignments)
            assign_elem!(state, 0, Val{c}, x, y) || return false
        end
    end
    # Start the main recursion for backtracking search.
    @timeit to "Start backtrack recursion" backtracking_search(f, state, 1)
end

# Recursive backtracking_search function
function backtracking_search(f, state::BacktrackingState, depth::Int)
    # Choose the next unassigned element.
    mrv, mrv_elem = @timeit to "find_mrv_elem" find_mrv_elem(state, depth)
    if isnothing(mrv_elem)
        # No unassigned elements remain, so we have a complete assignment.
        return f(ACSetTransformation(state.assignment, state.dom, state.codom))
    elseif mrv == 0
        # An element has no allowable assignment, so we must backtrack.
        return false
    end
    c, x = mrv_elem
    # Attempt all assignments of the chosen element.
    Y = state.codom
    for y in parts(Y, c)
        @timeit to "assign_elem" assign_elem!(state, depth, Val{c}, x, y) &&
                                 @timeit to "backtracking recursive call" backtracking_search(f, state, depth + 1) &&
                                                                          return true
        unassign_elem!(state, depth, Val{c}, x)
    end
    return false
end






# Checkerboard surjection - BenchmarkTools
# x = Int64[]
# y = Float64[]
# for n in 1:20
#     for j in 1:3
#         println(n)
#         component = path_graph(ReflexiveGraph, n)
#         checkerboard = box_product(component, component)
#         codom = add_loops(component)
#         checkH = @benchmark homomorphism($checkerboard, $codom)
#         for_x = Array{Int64,1}(undef, length(checkH.times))
#         fill!(for_x, n)
#         append!(x, for_x)
#         append!(y, checkH.times)
#     end
# end
# scatter([x], [y], title = "Homomorphism Function", xlabel = "Graph Dimensions (Path Graph Vertex count)", ylabel = "Single Hom Calculation Time (ns)")
# savefig("tempSur.png")
# length(x)
# length(y)

# Checkerboard injection - BenchmarkTools


# x = Int64[]
# y = Float64[]
# for n in 1:20
#     for j in 1:3
#         println(n)
#         component = path_graph(ReflexiveGraph, n)
#         checkerboard = box_product(component, component)
#         codom = add_loops(checkerboard)
#         checkH = @benchmark homomorphism($component, $codom)
#         for_x = Array{Int64,1}(undef, length(checkH.times))
#         fill!(for_x, n)
#         append!(x, for_x)
#         append!(y, checkH.times)
#     end
# end
# scatter([x], [y], title = "Homomorphism Function", xlabel = "Graph Dimensions (Path Graph Vertex count)", ylabel = "Single Hom Calculation Time (ns)")
# savefig("tempInj.png")
# length(x)
# length(y)



# after this go in and run the same datasets but with benchmarking being called on inside functions

reset_timer!(to::TimerOutput)
component = path_graph(ReflexiveGraph, 2)
checkerboard = box_product(component, component)
codom = add_loops(component)
checkH = homomorphism(checkerboard, codom)
# component = path_graph(ReflexiveGraph, 3)
# checkerboard = box_product(component, component)
# codom = add_loops(component)
# checkH = homomorphism(checkerboard, codom)
# component = path_graph(ReflexiveGraph, 4)
# checkerboard = box_product(component, component)
# codom = add_loops(component)
# checkH = homomorphism(checkerboard, codom)
show(to)



for n in 1:20
    for j in 1:3
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(component)
        checkH = homomorphism(checkerboard, codom)
    end
end

for n in 1:20
    for j in 1:3
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(checkerboard)
        checkH = homomorphism(component, codom)
    end
end