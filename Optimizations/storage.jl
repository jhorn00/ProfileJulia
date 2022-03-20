function iterative_backtracking_search(f, state::BacktrackingState, depth::Int) # SHOULD BE POSSIBLE TO JUST PASS F ONCE - fix later
    # istate = IterativeBacktrackingState(c, x, p, false, Iterators.Stateful(p))
    # push!(stk, istate)
    ##################################### HANDLE FIRST CASE #####################################
    # Choose the next unassigned element.
    mrv1, mrv_elem1 = find_mrv_elem(state, depth)
    if isnothing(mrv_elem1)
        # No unassigned elements remain, so we have a complete assignment.
        return f(ACSetTransformation(state.assignment, state.dom, state.codom))
    elseif mrv1 == 0
        # An element has no allowable assignment, so we must backtrack.
        return false
    end
    c1, x1 = mrv_elem1
    # Attempt all assignments of the chosen element.
    Y1 = state.codom
    p1 = parts(Y1, c1)
    istate = IterativeBacktrackingState(c1, x1, p1, false, Iterators.Stateful(p1), 1)
    push!(stk, istate)

    while !isempty(stk)
        currentState = first(stk)
        # didSomething = false
        for y in first(stk).iterator
            println("y: ", y)
            println("depth: ", currentState.depth)
            if assign_elem!(state, currentState.depth, Val{currentState.c}, currentState.x, y)
                println("assign_elem")
                # && return true
                if currentState.ret
                    println("ret is true")
                    pop!(stk)
                    currentState = first(stk)
                    currentState.ret = true
                    # didSomething = true
                    break
                end
                # recursive call
                # Choose the next unassigned element.
                mrv, mrv_elem = find_mrv_elem(state, currentState.depth)
                if isnothing(mrv_elem)
                    # No unassigned elements remain, so we have a complete assignment.
                    # return f(ACSetTransformation(state.assignment, state.dom, state.codom))
                    currentState.ret = f(ACSetTransformation(state.assignment, state.dom, state.codom))
                    println("This should be true, popped: ", f(ACSetTransformation(state.assignment, state.dom, state.codom)))
                    pop!(stk)
                    break
                elseif mrv == 0
                    println("mrv == 0, popping...")
                    # An element has no allowable assignment, so we must backtrack.
                    # return false
                    pop!(stk)
                    break
                end
                c, x = mrv_elem
                # Attempt all assignments of the chosen element.
                Y = state.codom
                p = parts(Y, c)
                istate = IterativeBacktrackingState(c, x, p, false, Iterators.Stateful(p), currentState.depth + 1)
                push!(stk, istate)
                println("pushed new state")
                break
            end
            unassign_elem!(state, currentState.depth, Val{currentState.c}, currentState.x)
            println("unassign_elem")
        end
        # return false
        if currentState.depth == 1 && currentState.ret
            return currentState.ret
        end
        if currentState.depth == 11
            return false
        end
        # else
        #     pop!(stk)
        # end
    end
    return false
end