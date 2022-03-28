# This is used to test homs with different functions
include("../Includes/iterativeBoilerplate.jl")
using DataStructures
import Catlab.CategoricalAlgebra.CSets: attr, adom, acodom, out_hom, quot

""" Internal state for backtracking search for ACSet homomorphisms.
"""
mutable struct IterativeBacktrackingState
    # needed to resume
    x::Int64
    iterator::Base.Iterators.Stateful{UnitRange{Int64},Union{Nothing,Tuple{Int64,Int64}}}
end

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
        t = @timeit to "assign call" assign_elem!(state, depth, Val{c}, x, y)
        t &&
            backtracking_search(f, state, depth + 1) &&
            return true
        unassign_elem!(state, depth, Val{c}, x)
    end
    return false
end

function find_mrv_elem(state::BacktrackingState{S}, depth) where {S}
    mrv, mrv_elem = Inf, nothing
    Y = state.codom
    for c in ob(S), (x, y) in enumerate(state.assignment[c])
        y == 0 || continue
        n = count(can_assign_elem(state, depth, Val{c}, x, y) for y in parts(Y, c))
        if n < mrv
            mrv, mrv_elem = n, (c, x)
        end
    end
    (mrv, mrv_elem)
end

""" Attempt to assign element (c,x) to (c,y) in the current assignment.
Returns whether the assignment succeeded. Note that the backtracking state can
be mutated even when the assignment fails.
"""
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
        X, Y = state.dom, state.codom
        $(map(zip(attr(S), adom(S), acodom(S))) do (f, c_, d)
            :($(quot(c_)) != c
              || state.type_components[$(quot(d))](subpart(X, x, $(quot(f))))
                 ==
                 subpart(Y, y, $(quot(f))) || return false)
        end...)

        # Make the assignment and recursively assign subparts.
        state.assignment.$c[x] = y
        state.assignment_depth.$c[x] = depth
        if !isnothing(state.inv_assignment.$c)
            state.inv_assignment.$c[y] = x
        end
        $(map(out_hom(S, c)) do (f, d)
            :(assign_elem!(state, depth, Val{$(quot(d))}, subpart(X, x, $(quot(f))),
                subpart(Y, y, $(quot(f)))) || return false)
        end...)
        return true
    end
end

""" Unassign the element (c,x) in the current assignment.
"""
@generated function unassign_elem!(state::BacktrackingState{S}, depth,
    ::Type{Val{c}}, x) where {S,c}
    quote
        state.assignment.$c[x] == 0 && return
        assign_depth = state.assignment_depth.$c[x]
        @assert assign_depth <= depth
        if assign_depth == depth
            X = state.dom
            if !isnothing(state.inv_assignment.$c)
                y = state.assignment.$c[x]
                state.inv_assignment.$c[y] = 0
            end
            state.assignment.$c[x] = 0
            state.assignment_depth.$c[x] = 0
            $(map(out_hom(S, c)) do (f, d)
                :(unassign_elem!(state, depth, Val{$(quot(d))},
                    subpart(X, x, $(quot(f)))))
            end...)
        end
    end
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
    iterative_backtracking_search(f, state)
end

function iterative_backtracking_search(f, state::BacktrackingState)
    # Make Linked List to use as stack.
    ll = MutableLinkedList{IterativeBacktrackingState}()
    ##################################### HANDLE FIRST CASE #####################################
    # Choose the next unassigned element.
    depth = 1
    mrv, mrv_elem = find_mrv_elem(state, depth)
    if isnothing(mrv_elem)
        # No unassigned elements remain, so we have a complete assignment.
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
        # If the iterator is over, pop.
        if isempty(currentState.iterator)
            popfirst!(ll)
            depth = depth - 1
            continue
        end
        # Values should be set if the depth and state are being visited for the first time.
        # Attempt all assignments of the chosen element.
        for y in currentState.iterator
            # I believe the time taken to run assign_elem is deceptively small.
            # find_mrv_elem, which takes the bulk of the process resources, makes multiple calls to it.
            # Therefore, speeding it up should give much better performance.
            t = @timeit to "assign call" assign_elem!(state, depth, Val{c}, currentState.x, y)
            @timeit to "if statement" if t
                # && return true
                depth = depth + 1
                mrv, mrv_elem = @timeit to "find_mrv_elem" find_mrv_elem(state, depth)
                # see if we can store these to run the function less - not possible
                if isnothing(mrv_elem)
                    # No unassigned elements remain, so we have a complete assignment.
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

# Compares the recursive and iterative solutions
# To my knowledge the ACSetTransformation has only 3 values - James Horn
function compareFunctions(acset1, acset2)
    # Ideally this can resolve compilation/GC issues
    ac2 = add_loops(acset2)
    original = @timeit to "original" homomorphism(acset1, ac2)
    iterative = @timeit to "iterative" ihomomorphism(acset1, ac2)
    println(original)
    println(iterative)
    # @time homomorphism(acset1, ac2)
    # @time ihomomorphism(acset1, ac2)
    # homO = @benchmark homomorphism($acset1, $ac2)
    # println(median(homO))
    # homI = @benchmark ihomomorphism($acset1, $ac2)
    # println(median(homI))
    # reset_timer!(to::TimerOutput)
    # original = @timeit to "recursive function" homomorphism(acset1, add_loops(acset2))
    # iterative = @timeit to "iterative function" ihomomorphism(acset1, add_loops(acset2))
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

# Unit tests
numSamples = 100
BenchmarkTools.DEFAULT_PARAMETERS.samples = numSamples
large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

compareFunctions(large1, large2)
reset_timer!(to::TimerOutput);
for n in 1:20 # number of vertices ranges from 1 to 20
    for j in 1:3 # runs each 3 times
        println(n)
        component = path_graph(ReflexiveGraph, n) # generate path graph of size n
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(component) # add loops to the codomain
        @time compareFunctions(checkerboard, component)
        # @timeit to "original" homomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***
        # @timeit to "iterative" ihomomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***
    end
end
show(to)
reset_timer!(to::TimerOutput)

"Lenient comparison operator for `struct`, both mutable and immutable (type with \\eqsim)."
    @generated function ≂(x, y)
        if !isempty(fieldnames(x)) && x == y
            mapreduce(n -> :(x.$n == y.$n), (a,b)->:($a && $b), fieldnames(x))
        else
            :(x == y)
        end
    end

function can_assign_elem(state::BacktrackingState, depth,
    ::Type{Val{c}}, x, y) where {c}
    # Although this method is nonmutating overall, we must temporarily mutate the
    # backtracking state, for several reasons. First, an assignment can be a
    # consistent at each individual subpart but not consistent for all subparts
    # simultaneously (consider trying to assign a self-loop to an edge with
    # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
    # must keep track of which elements we have visited to avoid looping forever.
    # println("before\n", state)
    ok = assign_elem!(state, depth, Val{c}, x, y)
    unassign_elem!(state, depth, Val{c}, x) # storing the state to revert is slower and consumes more memory
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
    oldAssign = deepcopy(state.assignment)
    oldDepth = deepcopy(state.assignment_depth) # could need deepcopy
    oldInv = deepcopy(state.inv_assignment)
    # println(state)
    ok = assign_elem!(state, depth, Val{c}, x, y)
    # println(state)
    state.assignment = oldAssign
    state.assignment_depth = oldDepth
    state.inv_assignment = oldInv
    # state = BacktrackingState(oldAssign, oldDepth, oldInv, state.dom, state.codom)
    # println(state)
    # unassign_elem!(state, depth, Val{c}, x) # storing the state to revert is slower and consumes more memory
    return ok
end

component = path_graph(ReflexiveGraph, 2) # generate path graph of size n
checkerboard = box_product(component, component) # generate grid graph based on the component graph
codom = add_loops(component) # add loops to the codomain
# @time compareFunctions(checkerboard, component)
homomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***
ihomomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***


compareFunctions(large1, large2)
reset_timer!(to::TimerOutput)
compareFunctions(large1, large2)
show(to)

compareFunctions(large6, large3)
reset_timer!(to::TimerOutput)
compareFunctions(large6, large3)
show(to)

compareFunctions(large7, large4)
reset_timer!(to::TimerOutput)
compareFunctions(large7, large4)
show(to)

# 1
compareFunctions(large1, large2)
compareFunctions(large1, large3)
compareFunctions(large1, large4)
compareFunctions(large1, large5)
compareFunctions(large1, large6)
compareFunctions(large1, large7)
#2
compareFunctions(large2, large1)
compareFunctions(large2, large3)
compareFunctions(large2, large4)
compareFunctions(large2, large5)
compareFunctions(large2, large6)
compareFunctions(large2, large7)
#3
compareFunctions(large3, large1)
compareFunctions(large3, large2)
compareFunctions(large3, large4)
compareFunctions(large3, large5)
compareFunctions(large3, large6)
compareFunctions(large3, large7)
#4
compareFunctions(large4, large1)
compareFunctions(large4, large2)
compareFunctions(large4, large3)
compareFunctions(large4, large5)
compareFunctions(large4, large6)
compareFunctions(large4, large7)
#5
compareFunctions(large5, large1)
compareFunctions(large5, large2)
compareFunctions(large5, large3)
compareFunctions(large5, large4)
compareFunctions(large5, large6)
compareFunctions(large5, large7)
#6
compareFunctions(large6, large1)
compareFunctions(large6, large2)
compareFunctions(large6, large3)
# The following comments take a long time to run.
# compareFunctions(large6, large4)
# compareFunctions(large6, large5)
# compareFunctions(large6, large7)
homomorphism(large6, add_loops(large4))
homomorphism(large6, large5)
homomorphism(large6, large7)
ihomomorphism(large6, large4)
ihomomorphism(large6, large5)
ihomomorphism(large6, large7)
#7
compareFunctions(large7, large1)
compareFunctions(large7, large2)
compareFunctions(large7, large3)
compareFunctions(large7, large4)
compareFunctions(large7, large5)
compareFunctions(large7, large6)