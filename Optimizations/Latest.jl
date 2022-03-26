# Storage file for the latest version of the iterative backtracking search.
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
        for y in first(ll).iterator
            if assign_elem!(state, depth, Val{c}, currentState.x, y)
                # && return true
                depth = depth + 1
                mrv, mrv_elem = find_mrv_elem(state, depth)
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
                newstate = IterativeBacktrackingState(x, Iterators.Stateful(p))
                pushfirst!(ll, newstate)
                break
            end
            unassign_elem!(state, depth, Val{c}, currentState.x)
        end
    end
    return false
end