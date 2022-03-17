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
struct IterativeBacktrackingState{S <: SchemaDescType,
  Assign <: NamedTuple, PartialAssign <: NamedTuple,
  Dom <: StructACSet{S}, Codom <: StructACSet{S}}
  """ The current assignment, a partially-defined homomorphism of ACSets. """
  assignment::Assign
  """ Depth in search tree at which assignments were made. """
  assignment_depth::Assign
  """ Inverse assignment for monic components or if finding a monomorphism. """
  inv_assignment::PartialAssign
  """ Domain ACSet: the "variables" in the CSP. """
  dom::Dom
  """ Codomain ACSet: the "values" in the CSP. """
  codom::Codom
  # make it iterative
  c::Symbol
  x::Int64
  Y::Catlab.Graphs.BasicGraphs.Graph
  parts::UnitRange{Int64}
  f::Any
  depth::Int64
  IterativeBacktrackingState() = new{NamedTuple, NamedTuple, NamedTuple, StructACSet{SchemaDescType}, StructACSet{SchemaDescType}}
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
  println("f: ", typeof(f), "\ndepth: ", typeof(depth))
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
  # state = new(IterativeBacktrackingState())
  # state.assignment = assignment
  # state.assignment_depth = assignment_depth
  # state.inv_assignment = inv_assignment
  # state.dom = X
  # state.codom = Y
  state = IterativeBacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)

  # Make any initial assignments, failing immediately if inconsistent.
  for (c, c_assignments) in pairs(initial)
    for (x, y) in partial_assignments(c_assignments)
      assign_elem!(state, 0, Val{c}, x, y) || return false
    end
  end

  # Start the main recursion for backtracking search.
  state.f = f
  state.depth = 1
  iterative_backtracking_search(state)
end

function iterative_backtracking_search(state::IterativeBacktrackingState{S}) where {S}
  stk.push(state)
  while !isempty(stk)
    ####################################################################################################
    # This part can remain the same for now.
    ####################################################################################################
    # Choose the next unassigned element.
    state.mrv, state.mrv_elem = find_mrv_elem(state, state.depth)
    if isnothing(state.mrv_elem)
      # No unassigned elements remain, so we have a complete assignment.
      return state.f(ACSetTransformation(state.assignment, state.dom, state.codom))
    elseif state.mrv == 0
      # An element has no allowable assignment, so we must backtrack.
      return false
    end
    state.c, state.x = state.mrv_elem

    ####################################################################################################
    # This part will see changes.
    ####################################################################################################
    # Attempt all assignments of the chosen element.
    state.Y = state.codom
    for y in parts(state.Y, state.c)
      if assign_elem!(state, state.depth, Val{state.c}, state.x, y)
        # make copy and iterate depth by 1
        newState = copy(state)
        newState.depth = newState.depth + 1
        if iterative_backtracking_search(newState)
          return true
        end
      end
      unassign_elem!(state, state.depth, Val{state.c}, state.x)
    end
    return false
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