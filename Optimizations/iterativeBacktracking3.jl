# This file aims to convert backtracking_search from recursive to iterative.
# This is the first attempt, using a stack.

# After including this if you wish to use TimerOutputs you should reset_timer
include("../Includes/iterativeBoilerplate.jl")
using DataStructures

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

####################################################################################################
# This is the struct we can use for the state
####################################################################################################

""" Internal state for backtracking search for ACSet homomorphisms.
"""
mutable struct IterativeBacktrackingState
    # needed to resume
    c::Symbol
    x::Int64
    parts::Any
    ret::Bool
    iterator::Iterators.Stateful
    depth::Int64
end

####################################################################################################
# Our version of the call stack. It can be moved to the initial function.
####################################################################################################

stk = Stack{IterativeBacktrackingState}()

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

####################################################################################################
# This is the initial call
####################################################################################################

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
    backtracking_search(f, state, 1)
end

####################################################################################################
# This is the recursive call. It will need to have a stack to replace the calls to itself.
####################################################################################################
function backtracking_search(f, state::BacktrackingState, depth::Int)
    # Choose the next unassigned element.
    mrv, mrv_elem = find_mrv_elem(state, depth)
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

####################################################################################################
# This is the iterative call.
####################################################################################################
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
    iterative_backtracking_search(f, state, 1)
end

function iterative_backtracking_search(f, state::BacktrackingState, depth::Int)
    ##################################### HANDLE FIRST CASE #####################################
    # Choose the next unassigned element.
    mrv, mrv_elem = find_mrv_elem(state, depth)
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
    p = parts(Y, c)
    istate = IterativeBacktrackingState(c, x, p, false, Iterators.Stateful(p), 1)
    push!(stk, istate)
    justPopped = false
    enteredFor = true
    while !isempty(stk)
        currentState = first(stk)
        if !enteredFor
            pop!(stk)
            justPopped = true
            enteredFor = true
            println("enteredFor continue")
            continue
        else
            enteredFor = false
        end

        # Choose the next unassigned element.
        mrv, mrv_elem = find_mrv_elem(state, currentState.depth)
        if isnothing(mrv_elem)
            # No unassigned elements remain, so we have a complete assignment.
            currentState.ret = f(ACSetTransformation(state.assignment, state.dom, state.codom))
            pop!(stk)
            justPopped = true
            enteredFor = true
            # continue <- was this, but with iterative we can break
            println("isnothing continue")
            continue
        elseif mrv == 0
            # An element has no allowable assignment, so we must backtrack.
            pop!(stk)
            justPopped = true
            enteredFor = true
            println("mrv == 0 continue")
            println(currentState.x)
            println(currentState.depth)
            unassign_elem!(state, currentState.depth - 1, Val{currentState.c}, currentState.x) # may need to calc these - print them out before unassign_elem - may need to make sure we dont get a depth of 0 or something
            continue
        end

        if !justPopped
            c, x = mrv_elem
            # Attempt all assignments of the chosen element.
            Y = state.codom
            p = parts(Y, c)
            currentState.parts = p
            currentState.iterator = Iterators.Stateful(p)
        else
            justPopped = false
        end
        for y in first(stk).iterator
            println("y: ", y)
            println("depth: ", currentState.depth)
            enteredFor = true
            if y == 1
                currentState.c = c
                currentState.x = x
            end
            println("x: ", currentState.x)
            t = assign_elem!(state, currentState.depth, Val{currentState.c}, currentState.x, y)
            if (currentState.depth == 12 && (y == 6 || y == 7 || y == 8 || y == 9)) || (currentState.depth == 13 && y == 1)
                println("assign_elem: ", t)
                println("state: ", state)
                println("depth: ", currentState.depth)
                println("Val: ", Val{currentState.c})
                println("x: ", currentState.x)
                println("y: ", y)
            end
            if t
                # && return true
                if currentState.ret
                    pop!(stk)
                    currentState = first(stk)
                    currentState.ret = true
                    println("ret = true break (inside assign_elem)")
                    break
                end
                newstate = IterativeBacktrackingState(c, x, p, false, Iterators.Stateful(p), currentState.depth + 1)
                push!(stk, newstate)
                println("break after push (inside assign_elem)")
                break
            end
            unassign_elem!(state, currentState.depth, Val{currentState.c}, currentState.x)
            println("unassign_elem")
            # assigned = false
            if y == length(first(stk).parts)
                pop!(stk)
                justPopped = true
            end
        end
        # return false
        if currentState.depth == 1 && currentState.ret
            return currentState.ret
        end
        # if currentState.depth == 15
        #     return false
        # end
    end
    return false
end

# gtoh = homomorphism(g, h_codom)

large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

# homomorphism(large1, add_loops(a_sparse_five))
# homomorphism(large2, add_loops(a_sparse_three))
# homomorphism(large3, add_loops(a_sparse_seven))
# h = homomorphism(large4, add_loops(a_sparse_eight))
# draw(h)

# homomorphism(large5, add_loops(large2))
# homomorphism(large6, add_loops(large3))
# homomorphism(large7, add_loops(large4))
# homomorphism(large1, add_loops(a_sparse_three))
# homomorphism(large2, add_loops(a_sparse_six))
# homomorphism(large3, add_loops(a_sparse_eight))
homomorphism(large4, add_loops(large1)) # THIS ONE BREAKS - When looking at it the values are wrong for the depth
# homomorphism(large5, add_loops(large3))
# homomorphism(a_sparse_eight, add_loops(a_sparse_seven))
# homomorphism(a_sparse_eight2, add_loops(a_sparse_six))
# homomorphism(a_sparse_five, add_loops(a_sparse_three))
# homomorphism(a_sparse_six2, add_loops(a_sparse_four))
