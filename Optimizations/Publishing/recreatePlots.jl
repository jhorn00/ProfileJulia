using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
using TimerOutputs
draw(g) = to_graphviz(g, node_labels=true, edge_labels=true)
GraphvizGraphs.to_graphviz(f::ACSetTransformation; kw...) =
    to_graphviz(GraphvizGraphs.to_graphviz_property_graph(f; kw...))

function GraphvizGraphs.to_graphviz_property_graph(f::ACSetTransformation; kw...)
    pg = GraphvizGraphs.to_graphviz_property_graph(dom(f); kw...)
    vcolors = hex.(range(colorant"#0021A5", stop=colorant"#FA4616", length=nparts(codom(f), :V)))
    ecolors = hex.(range(colorant"#6C9AC3", stop=colorant"#E28F41", length=nparts(codom(f), :E)))
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
include("../../Includes/graph_bank.jl")
include("../../Includes/autoplot.jl")

# homomorphisms imports
import Catlab.CategoricalAlgebra.CSets: homomorphisms, homomorphism
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components

# backtracking_search imports
import Catlab.Theories: SchemaDescType
import Catlab.CategoricalAlgebra.CSets: BacktrackingState, find_mrv_elem, can_assign_elem, quot
import Catlab.CategoricalAlgebra.CSets: find_mrv_elem, assign_elem!, unassign_elem!, out_attr, out_hom

# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    result = nothing
    @timeit to "homomorphism() call" homomorphisms(X, Y; kw...) do α
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
homomorphisms(f, X::StructACSet, Y::StructACSet; monic=false, iso=false, initial=(;)) = @timeit to "initial backtracking_search() call" backtracking_search(f, X, Y, monic=monic, iso=iso, initial=initial)

# Backtracking
function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
    monic=false, iso=false, initial=(;)) where {Ob,S<:SchemaDescType{Ob}}
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
    @timeit to "start backtrack recursion" backtracking_search(f, state, 1)
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
        assign_elem!(state, depth, Val{c}, x, y) &&
            backtracking_search(f, state, depth + 1) &&
            return true
        unassign_elem!(state, depth, Val{c}, x)
    end
    return false
end

################### G larger than H for G->H ###################
const to = TimerOutput()
large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

reset_timer!(to::TimerOutput)
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
# show(to)
show(TimerOutputs.flatten(to))

""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState{S}, depth) where {S}
    mrv, mrv_elem = Inf, nothing
    Y = state.codom
    for c in ob(S), (x, y) in enumerate(state.assignment[c])
        y == 0 || continue
        n = count(@timeit to "calls can_assign_elem with state saving" can_assign_elem(state, depth, Val{c}, x, y) for y in parts(Y, c))
        if n < mrv
            mrv, mrv_elem = n, (c, x)
        end
    end
    (mrv, mrv_elem)
end

function can_assign_elem(state::BacktrackingState, depth,
    ::Type{Val{c}}, x, y) where {c}
    # Although this method is nonmutating overall, we must temporarily mutate the
    # backtracking state, for several reasons. First, an assignment can be a
    # consistent at each individual subpart but not consistent for all subparts
    # simultaneously (consider trying to assign a self-loop to an edge with
    # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
    # must keep track of which elements we have visited to avoid looping forever.
    ok = @timeit to "assign_elem in can_assign_elem" assign_elem!(state, depth, Val{c}, x, y)
    @timeit to "unassign_elem in can_assign_elem" unassign_elem!(state, depth, Val{c}, x) # storing the state to revert is slower and consumes more memory
    return ok
end

function can_assign_elem(state::BacktrackingState, depth,
    ::Type{Val{c}}, x, y) where {c}
    # Although this method is nonmutating overall, we must temporarily mutate the
    # backtracking state, for several reasons. First, an assignment can be a
    # consistent at each individual subpart but not consistent for all subparts
    # simultaneously (consider trying to assign a self-loop to an edge with
    # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
    # must keep track of which elements we have visited to avoid looping forever.
    orig_state = deepcopy(state)
    d = copy(depth)
    # cc = c
    xx = copy(x)
    yy = copy(y)
    ok = assign_elem!(state, depth, Val{c}, x, y)
    state = orig_state
    depth = d
    # c = cc
    x = xx
    y = yy
    # @timeit to "unassign_elem in can_assign_elem" unassign_elem!(state, depth, Val{c}, x) # storing the state to revert is slower and consumes more memory
    return ok
end