# This is used to test homs with different functions
include("../Includes/iterativeBoilerplate.jl")
using DataStructures

mutable struct CaptureState
    state::BacktrackingState
    y::Any
    depth::Int64
    c::Any
    x::Any
    t::Any
end

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

stk = Stack{IterativeBacktrackingState}()

ihomomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
    ihomomorphism(X, Y, alg; kw...)

function ihomomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
    result = nothing
    iterative_backtracking_search(X, Y; kw...) do α
        result = α
        return true
    end
    result
end

ihomomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
    ihomomorphisms(X, Y, alg; kw...)

function ihomomorphisms(X::StructACSet{S}, Y::StructACSet{S},
    alg::BacktrackingSearch; kw...) where {S}
    results = ACSetTransformation{S}[]
    iterative_backtracking_search(X, Y; kw...) do α
        push!(results, map_components(deepcopy, α))
        return false
    end
    results
end

homomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
    homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
    result = nothing
    backtracking_search(X, Y; kw...) do α
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
    backtracking_search(X, Y; kw...) do α
        push!(results, map_components(deepcopy, α))
        return false
    end
    results
end

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
        t = assign_elem!(state, depth, Val{c}, x, y)
        enqueue!(original_states, CaptureState(deepcopy(state), y, depth, c, x, t))
        t &&
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
            continue
        elseif mrv == 0
            # An element has no allowable assignment, so we must backtrack.
            pop!(stk)
            justPopped = true
            enteredFor = true
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
            enteredFor = true
            if y == 1
                currentState.c = c
                currentState.x = x
            end
            t = assign_elem!(state, currentState.depth, Val{currentState.c}, currentState.x, y)
            enqueue!(iterative_states, CaptureState(deepcopy(state), y, currentState.depth, currentState.c, currentState.x, t))
            if t
                # && return true
                if currentState.ret
                    pop!(stk)
                    currentState = first(stk)
                    currentState.ret = true
                    break
                end
                newstate = IterativeBacktrackingState(c, x, p, false, Iterators.Stateful(p), currentState.depth + 1)
                push!(stk, newstate)
                break
            end
            unassign_elem!(state, currentState.depth, Val{currentState.c}, currentState.x)
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
    end
    return false
end

# Compares the recursive and iterative solutions
# To my knowledge the ACSetTransformation has only 3 values - James Horn
function compareFunctions(acset1, acset2)
    original = homomorphism(acset1, add_loops(acset2))
    iterative = ihomomorphism(acset1, add_loops(acset2))
    println("\n==================\nComparison Results\n------------------")
    if original == iterative
        println("Equivalent\n==================\n")
    elseif original.components != iterative.components
        println("The components differ.\n------------------")
        println("Original Hom method result:\n", original.components)
        println("------------------\nIterative Hom method result:\n", iterative.components, "\n==================\n")
    else
        println("Unexpected error encountered.\n------------------")
        println("Original Hom method result:\n", original)
        println("------------------\nIterative Hom method result:\n", iterative, "\n==================\n")
    end
end

Base.copy

# Trying to figure out this tricky bug
original_states = Queue{Any}()
iterative_states = Queue{Any}()

large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

homomorphism(large5, add_loops(large2))
ihomomorphism(large5, add_loops(large2))

homomorphism(large6, add_loops(large3))
ihomomorphism(large6, add_loops(large3))

homomorphism(large7, add_loops(large4))
ihomomorphism(large7, add_loops(large4))

homomorphism(large1, add_loops(a_sparse_three))
ihomomorphism(large1, add_loops(a_sparse_three))




original_states = Queue{Any}()
iterative_states = Queue{Any}()

# this one
homomorphism(large4, add_loops(large1))
ihomomorphism(large4, add_loops(large1))
########################################

length(original_states)
length(iterative_states)

function firstDivergence()
    original_history::Any = nothing
    iterative_history::Any = nothing
    while !isempty(original_states) && !isempty(iterative_states)
        println("runs")
        println(first(original_states).y)
        println(first(iterative_states).y)
        println(first(original_states).state.assignment.V)
        println(first(iterative_states).state.assignment.V)
        println(first(original_states).state.assignment.E)
        println(first(iterative_states).state.assignment.E)
        println(first(original_states).depth)
        if (first(original_states).depth != first(iterative_states).depth)
            println("\n\n\nDivergence encountered.\nOriginal:\ny: ", first(original_states).y, "\ndepth: ", first(original_states).depth, "t: ", first(original_states).t)
            println("Iterative:\ny: ", first(iterative_states).y, "\ndepth: ", first(iterative_states).depth, "t: ", first(iterative_states).t)
            println("\nOriginal:\n", first(original_states).state.assignment)
            println("\nIterative:\n", first(iterative_states).state.assignment)
            println("\n\n\nPrevious:\n")
            println("Original:\n", original_history)
            println("\nIterative:\n", iterative_history)
            break
        else
            original_history = first(original_states).state.assignment
            iterative_history = first(iterative_states).state.assignment
        end
        dequeue!(original_states)
        dequeue!(iterative_states)
    end
    # println(first(original_states).state.assignment == first(iterative_states).state.assignment)
end
firstDivergence()

println(last(original_states))
println(first(original_states))