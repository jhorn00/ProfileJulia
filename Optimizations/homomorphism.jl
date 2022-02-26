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
include("../Revised Files/graph_bank.jl")
include("../Revised Files/autoplot.jl")

# homomorphisms imports
import Catlab.CategoricalAlgebra.CSets: homomorphisms, homomorphism
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components

# backtracking_search imports
import Catlab.Theories: SchemaDescType
import Catlab.CategoricalAlgebra.CSets: BacktrackingState, find_mrv_elem, can_assign_elem, quot
import Catlab.CategoricalAlgebra.CSets: find_mrv_elem, assign_elem!, unassign_elem!, out_attr, out_hom

################################### Run the above code ###################################

const to = TimerOutput()

# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    result = nothing
    homomorphisms(X, Y; kw...) do α
        result = α
        return true
    end
    result
end


# it uses two homomorphisms functions
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S}; kw...) where {S}
    results = ACSetTransformation{S}[]
    homomorphisms(X, Y; kw...) do α
        push!(results, map_components(deepcopy, α))
        return false
    end
    results
end
homomorphisms(f, X::StructACSet, Y::StructACSet; monic = false, iso = false, initial = (;)) = backtracking_search(f, X, Y, monic = monic, iso = iso, initial = initial)

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
    # println("Initial State:\n", state)
    backtracking_search(f, state, 1)
end

# Recursive backtracking_search function
function backtracking_search(f, state::BacktrackingState, depth::Int)
    # Choose the next unassigned element.
    mrv, mrv_elem = find_mrv_elem(state, depth)
    if isnothing(mrv_elem)
        # No unassigned elements remain, so we have a complete assignment.
        return f(ACSetTransformation(state.assignment, state.dom, state.codom))
    elseif mrv == 0
        # An element has no allowable assignment, so we must backtrack.
        # println("State before backtrack:\n", state)
        return false
    end
    c, x = mrv_elem
    # Attempt all assignments of the chosen element.
    # Y = state.codom
    for y in parts(state.codom, c)
        # println("State for y in parts:\n", state)
        assign_elem!(state, depth, Val{c}, x, y) &&
            backtracking_search(f, state, depth + 1) &&
            return true
        unassign_elem!(state, depth, Val{c}, x)
    end
    # println("State before return false:\n", state)
    return false
end


""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState{S}, depth) where {S}
    mrv, mrv_elem = Inf, nothing
    # Y = state.codom
    for c in ob(S), (x, y) in enumerate(state.assignment[c])
        y == 0 || continue
        n = count(can_assign_elem(state, depth, Val{c}, x, y) for y in parts(state.codom, c))
        if n < mrv
            mrv, mrv_elem = n, (c, x)
        end
    end
    (mrv, mrv_elem)
end


@generated function assign_elem!(state::BacktrackingState{S}, depth,
    ::Type{Val{c}}, x, y) where {S,c}
    quote
        y′ = state.assignment.$c[x]
        y′ == y && return true  # If x is already assigned to y, return immediately.
        y′ == 0 || return false # Otherwise, x must be unassigned.
        if !isnothing(state.inv_assignment.$c) && state.inv_assignment.$c[y] != 0
            # Also, y must unassigned in the inverse assignment.
            return false
        end

        # Check attributes first to fail as quickly as possible.
        # X, Y = state.dom, state.codom
        $(map(out_attr(S, c)) do f
            :(subpart(state.dom, x, $(quot(f))) == subpart(state.codom, y, $(quot(f))) || return false)
        end...)

        # Make the assignment and recursively assign subparts.
        state.assignment.$c[x] = y
        state.assignment_depth.$c[x] = depth
        if !isnothing(state.inv_assignment.$c)
            state.inv_assignment.$c[y] = x
        end
        $(map(out_hom(S, c)) do (f, d)
            :(assign_elem!(state, depth, Val{$(quot(d))}, subpart(state.dom, x, $(quot(f))),
                subpart(state.codom, y, $(quot(f)))) || return false)
        end...)
        return true
    end
end

g = @acset Graphs.Graph begin
    V = 5
    E = 5
    src = [1, 2, 3, 3, 4]
    tgt = [3, 3, 4, 5, 5]
end
g_codom = add_loops(g)
# draw(g)
h = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 1, 2]
    tgt = [2, 3, 3]
end
h_codom = add_loops(h)
# draw(h)


reset_timer!(to::TimerOutput)
gtoh = homomorphism(g, h_codom)
htog = homomorphism(h, g_codom)
show(TimerOutputs.flatten(to))
# collect(gtoh[:V])
# collect(gtoh[:E])
draw(gtoh)
draw(htog)

if gtoh == htog
    println("equal")
else
    println("not equal")
end


test = homomorphism(a_sparse_three, add_loops(a_sparse_four))
draw(test)

test = homomorphism(a_sparse_four, add_loops(a_sparse_eight))
draw(test)

# component = path_graph(ReflexiveGraph, 2) # generate path graph of size n
# checkerboard = box_product(component, component) # generate grid graph based on the component graph
# codom_val = add_loops(component) # add loops to the codomain
# checkH = homomorphism(checkerboard, codom_val) # generate homomorphism ***GRID -> PATH***
# draw(checkH) # this does not work
# draw(component)
# draw(checkerboard)
# draw(codom_val)



# testing if it will change the old value (it will not)
# function myTest(test)
#     X = test.dom
#     Y = test.codom
#     println("Inside before: ", X, "\n and test is: ", test.dom)
#     X = g
#     println("Inside: ", X, "\nand test is: ", test.dom)
# end
# myTest(test)
# println("Outside: ", test.dom, "\nand g is: ", g)

x = 0
myTest(x)
println(x)