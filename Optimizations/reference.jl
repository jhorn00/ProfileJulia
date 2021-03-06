####################################################################################################
# This is the struct we can use for the state
####################################################################################################

""" Internal state for backtracking search for ACSet homomorphisms.
"""
struct BacktrackingState{S <: SchemaDescType,
  Assign <: NamedTuple, PartialAssign <: NamedTuple, LooseFun <: NamedTuple,
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
type_components::LooseFun
end

####################################################################################################
# This is the initial call
####################################################################################################

function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
                           monic=false, iso=false, type_components=(;), initial=(;),
                           ) where {Ob, Hom, Attr, S<:SchemaDescType{Ob,Hom,Attr}}
# Fail early if no monic/isos exist on cardinality grounds.
if iso isa Bool
  iso = iso ? Ob : ()
end
for c in iso
  nparts(X,c) == nparts(Y,c) || return false
end
if monic isa Bool
  monic = monic ? Ob : ()
end
# Injections between finite sets are bijections, so reduce to that case.
monic = unique([iso..., monic...])
for c in monic
  nparts(X,c) <= nparts(Y,c) || return false
end

# Initialize state variables for search.
assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
assignment_depth = map(copy, assignment)
inv_assignment = NamedTuple{Ob}(
  (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
loosefuns = NamedTuple{Attr}(
  isnothing(type_components) ? identity : get(type_components, c, identity) for c in Attr)
state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y,
                          loosefuns)

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

function backtracking_search(f, state::BacktrackingState{S}, depth::Int) where {S}
# Choose the next unassigned element.
mrv, mrv_elem = find_mrv_elem(state, depth)
if isnothing(mrv_elem)
  # No unassigned elements remain, so we have a complete assignment.
  if any(!=(identity), state.type_components)
    return f(LooseACSetTransformation{S}(
      state.assignment, state.type_components, state.dom, state.codom))
  else
    return f(ACSetTransformation(state.assignment, state.dom, state.codom))
  end
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