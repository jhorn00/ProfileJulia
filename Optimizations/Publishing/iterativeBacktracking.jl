# This file contains an iterative rewrite of the backtracking_search function.
# File last updated 3/28/2022 by James Horn

# After including this if you wish to use TimerOutputs you should reset_timer
include("../../Includes/iterativeBoilerplate.jl")
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

####################################################################################################
# This is the struct we can use for the state
####################################################################################################

""" Internal state for iterative backtracking search for ACSet homomorphisms.
"""
mutable struct IterativeBacktrackingState
    x::Int64
    iterator::Base.Iterators.Stateful{UnitRange{Int64},Union{Nothing,Tuple{Int64,Int64}}}
end

ihomomorphism(X::ACSet, Y::ACSet; alg = BacktrackingSearch(), kw...) =
  ihomomorphism(X, Y, alg; kw...)

function ihomomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
  result = nothing
  iterative_backtracking_search(X, Y; kw...) do α
    result = α
    return true
  end
  result
end

ihomomorphisms(X::ACSet, Y::ACSet; alg = BacktrackingSearch(), kw...) =
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

gtoh = homomorphism(g, h_codom)
igtoh = ihomomorphism(g, h_codom)
gtoh == igtoh