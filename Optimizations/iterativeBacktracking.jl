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
  # original components
  B::BacktrackingState
  f::Any
  depth::Int64
  # needed to resume
  c::Symbol
  x::Int64
  parts::Any
  ret::Bool
  iterator::Iterators.Stateful
end

####################################################################################################
# Our version of the call stack. It can be moved to the initial function.
####################################################################################################

stk = Stack{IterativeBacktrackingState}()

homomorphism(X::ACSet, Y::ACSet; alg = BacktrackingSearch(), kw...) =
  homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
  result = nothing
  iterative_backtracking_search(X, Y; kw...) do α
    result = α
    return true
  end
  result
end

homomorphisms(X::ACSet, Y::ACSet; alg = BacktrackingSearch(), kw...) =
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



  mrv, mrv_elem = find_mrv_elem(state, 1)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    return f(ACSetTransformation(state.assignment, state.dom, state.codom))
  elseif mrv == 0
    # An element has no allowable assignment, so we must backtrack.
    return false
  end
  c, x = mrv_elem

  # c::Symbol
  # x::Int64
  # Y::Catlab.Graphs.BasicGraphs.Graph
  # parts::UnitRange{Int64}
  # f::Any
  # depth::Int64


  # # original components
  # B::BacktrackingState
  # f::Any
  # depth::Int64
  # # needed to resume
  # c::Symbol
  # x::Int64
  # parts::Any


  # Start the main recursion for backtracking search.
  istate = IterativeBacktrackingState(state, f, 1, c, x, parts(state.codom, c), false, Iterators.Stateful(parts(state.codom, c))) ###depth might need to adjust or else it would run twice
  iterative_backtracking_search(istate)
end

function iterative_backtracking_search(state::IterativeBacktrackingState) # SHOULD BE POSSIBLE TO JUST PASS F ONCE - fix later
  push!(stk, state)
  while !isempty(stk)
    currentState = first(stk)
    # Attempt all assignments of the chosen element.
    Y = currentState.B.codom
    for y in currentState.iterator
      println("y: ", y)
      println("depth: ", currentState.depth)
      if currentState.depth == 20
        break
      end
      if assign_elem!(currentState.B, currentState.depth, Val{currentState.c}, currentState.x, y)
        println("assign_elem")
        if currentState.ret
          pop!(stk)
          currentState = first(stk)
          currentState.ret = true
          break
        end
        # make copy and iterate depth by 1
        # newState = copy(state) # This new one gets a depth of state.depth + 1
        # Choose the next unassigned element.
        mrv, mrv_elem = find_mrv_elem(currentState.B, currentState.depth) # pass in the BacktrackingSearch obj
        println("mrv_elem: ", mrv_elem)
        if isnothing(mrv_elem)
          # No unassigned elements remain, so we have a complete assignment.
          ans = state.f(ACSetTransformation(currentState.B.assignment, currentState.B.dom, currentState.B.codom))
          println("\n\n\n\nThe ACSET thing returns ", ans)
          currentState.ret = ans
          break # breaks out of for loop
        # return ans
        elseif mrv == 0
          # An element has no allowable assignment, so we must backtrack.
          # return false
          pop!(stk)
          break # breaks out of for loop
        end
        c, x = mrv_elem
        p = parts(Y, c)
        println("new thing made")
        newState = IterativeBacktrackingState(currentState.B, currentState.f, currentState.depth + 1, c, x, p, false, Iterators.Stateful(p))
        # need to investigate this new state but be able to return to this spot
        push!(stk, newState)
        break
        # if iterative_backtracking_search(newState)
        # return true
        # end
      end
      unassign_elem!(currentState.B, currentState.depth, Val{currentState.c}, currentState.x)
    end
    # return false
    pop!(stk)
    if currentState.depth == 20
      return false
    end
  end
end

gtoh = homomorphism(g, h_codom)

# c is V or E
# x often appears as an Int
# Y is a graph

# This is c:
# Symbol
# This is x:
# Int64
# this is Y:
# Catlab.Graphs.BasicGraphs.Graph
# Parts(Y, c) is a UnitRange{Int64}

# used typeof to get them