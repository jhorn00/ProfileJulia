include("../../Includes/iterativeBoilerplate.jl")
using DataStructures

const SUITE = BenchmarkGroup()

# How can I model this like the existing benchmark functions?

n = 10
SUITE["grids"] = BenchmarkGroup()
SUITE["grids"]["gridToPath"] = @benchmarkable gridToPath($n)
SUITE["grids"]["pathToGrid"] = @benchmarkable pathToGrid($n)

# Reflexive Graphs
function gridToPath(n)
    for i in 1:n
        component = path_graph(ReflexiveGraph, i) # generate path graph of size i
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(component) # add loops to the codomain
        homomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***
    end
end

function pathToGrid(n)
    for i in 1:n
        component = path_graph(ReflexiveGraph, i) # generate path graph of size i
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(checkerboard) # add loops to the codomain
        homomorphism(component, codom) # generate homomorphism ***PATH -> GRID***
    end
end

SUITE["gtoh"] = BenchmarkGroup()
SUITE["gtoh"]["gLarger"] = @benchmarkable gLarger()
SUITE["gtoh"]["hLarger"] = @benchmarkable hLarger()
SUITE["gtoh"]["analogous"] = @benchmarkable analogous()

# Generate larger graphs
large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

# G larger than H for G->H
loop_large1 = add_loops(large1)
loop_large2 = add_loops(large2)
loop_large3 = add_loops(large3)
loop_large4 = add_loops(large4)
loop_sparse_three = add_loops(a_sparse_three)
loop_sparse_four = add_loops(a_sparse_four)
loop_sparse_five = add_loops(a_sparse_five)
loop_sparse_six = add_loops(a_sparse_six)
loop_sparse_seven = add_loops(a_sparse_seven)
loop_sparse_eight = add_loops(a_sparse_eight)


function gLarger()
    homomorphism(a_sparse_six2, loop_sparse_four)
    homomorphism(a_sparse_eight, loop_sparse_seven)
    homomorphism(a_sparse_eight2, loop_sparse_six)
    homomorphism(a_sparse_five, loop_sparse_three)
    homomorphism(large1, loop_sparse_five)
    homomorphism(large1, loop_sparse_three)
    homomorphism(large2, loop_sparse_three)
    homomorphism(large2, loop_sparse_six)
    homomorphism(large3, loop_sparse_seven)
    homomorphism(large3, loop_sparse_eight)
    homomorphism(large4, loop_sparse_eight)
    homomorphism(large4, loop_large1)
    homomorphism(large5, loop_large2)
    homomorphism(large5, loop_large3)
    homomorphism(large6, loop_large3)
    homomorphism(large7, loop_large4)
end

# H larger than G for G->H
loop_sparse_six2 = add_loops(a_sparse_six2)
loop_sparse_eight2 = add_loops(a_sparse_eight2)
loop_large5 = add_loops(large5)
loop_large6 = add_loops(large6)
loop_large7 = add_loops(large7)

function hLarger()
    homomorphism(a_sparse_four, loop_sparse_six2)
    homomorphism(a_sparse_seven, loop_sparse_eight)
    homomorphism(a_sparse_six, loop_sparse_eight2)
    homomorphism(a_sparse_three, loop_sparse_five)
    homomorphism(a_sparse_five, loop_large1)
    homomorphism(a_sparse_three, loop_large1)
    homomorphism(a_sparse_three, loop_large2)
    homomorphism(a_sparse_six, loop_large2)
    homomorphism(a_sparse_seven, loop_large3)
    homomorphism(a_sparse_eight, loop_large3)
    homomorphism(a_sparse_eight, loop_large4)
    homomorphism(large1, loop_large4)
    homomorphism(large2, loop_large5)
    homomorphism(large3, loop_large5)
    homomorphism(large3, loop_large6)
    homomorphism(large4, loop_large7)
end

# G similar in size to H for G->H
function analogous()
    homomorphism(a_sparse_five, loop_sparse_five)
    homomorphism(a_sparse_eight, loop_sparse_eight)
    homomorphism(a_sparse_seven, loop_sparse_eight2)
    homomorphism(a_sparse_eight, loop_sparse_seven)
    homomorphism(a_sparse_three, loop_sparse_four)
    homomorphism(a_sparse_six, loop_sparse_five)
    homomorphism(a_sparse_four, loop_sparse_five)
    homomorphism(a_sparse_five, loop_sparse_four)
    homomorphism(a_sparse_four, loop_sparse_three)
    homomorphism(a_sparse_seven, loop_sparse_eight)
    homomorphism(a_sparse_six, loop_sparse_six2)
    homomorphism(a_sparse_six2, loop_sparse_five)
    homomorphism(a_sparse_five, loop_sparse_six2)
end

# Tune and run
tune!(SUITE);

results = run(SUITE, verbose=true, seconds=5)

""" Internal state for iterative backtracking search for ACSet homomorphisms.
"""
mutable struct IterativeBacktrackingState
    x::Int64
    iterator::Base.Iterators.Stateful{UnitRange{Int64},Union{Nothing,Tuple{Int64,Int64}}}
end

import Catlab.CategoricalAlgebra.CSets: homomorphism

homomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
    homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
    result = nothing
    iterative_backtracking_search(X, Y; kw...) do α
        result = α
        return true
    end
    result
end

homomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
    homomorphisms(X, Y, alg; kw...)

function homomorphisms(X::StructACSet{S}, Y::StructACSet{S},
    alg::BacktrackingSearch; kw...) where {S}
    results = ACSetTransformation{S}[]
    iterative_backtracking_search(X, Y; kw...) do α
        push!(results, map_components(deepcopy, α))
        return false
    end
    results
end

"""Initial iterative call"""
function iterative_backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
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
    iterative_backtracking_search(f, state)
end

function iterative_backtracking_search(f, state::BacktrackingState)
    # Linked list to behave as call stack.
    ll = MutableLinkedList{IterativeBacktrackingState}()
    # Handling the first state.
    # Set depth and choose the next unassigned element.
    depth = 1
    mrv, mrv_elem = find_mrv_elem(state, depth)
    if isnothing(mrv_elem)
        # If no unassigned elements remain, we can return.
        return f(ACSetTransformation(state.assignment, state.dom, state.codom))
    elseif mrv == 0
        # An element has no allowable assignment, so we must backtrack.
        return false
    end
    # Construct first IterativeBacktrackingState and add it to the stack.
    c, x = mrv_elem
    Y = state.codom
    p = parts(Y, c)
    istate = IterativeBacktrackingState(x, Iterators.Stateful(p))
    pushfirst!(ll, istate)
    # Create tracker variable(s).
    while !isempty(ll)
        # Get currentState based on stack.
        currentState = first(ll)
        # If the iterator is empty, pop.
        if isempty(currentState.iterator)
            popfirst!(ll)
            depth = depth - 1
            continue
        end
        # Values should be set if the depth and state are being visited for the first time.
        # Attempt all assignments of the chosen element.
        for y in currentState.iterator
            if assign_elem!(state, depth, Val{c}, currentState.x, y)
                depth = depth + 1
                mrv, mrv_elem = find_mrv_elem(state, depth)
                if isnothing(mrv_elem)
                    # If no unassigned elements remain, we can return.
                    if f(ACSetTransformation(state.assignment, state.dom, state.codom))
                        return true
                    else
                        depth = depth - 1
                        unassign_elem!(state, depth, Val{c}, currentState.x)
                        continue
                    end
                elseif mrv == 0
                    # An element has no allowable assignment, so we must backtrack.
                    depth = depth - 1
                    unassign_elem!(state, depth, Val{c}, currentState.x)
                    continue
                end
                # Construct new IterativeBacktrackingState and add it to the stack.
                c, x = mrv_elem
                p = parts(Y, c)
                istate = IterativeBacktrackingState(x, Iterators.Stateful(p))
                pushfirst!(ll, istate)
                break
            end
            unassign_elem!(state, depth, Val{c}, currentState.x)
        end
    end
    return false
end