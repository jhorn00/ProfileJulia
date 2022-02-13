using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
using TimerOutputs
draw(g) = to_graphviz(g, node_labels = true, edge_labels = true)
GraphvizGraphs.to_graphviz(f::ACSetTransformation; kw...) =
    to_graphviz(GraphvizGraphs.to_graphviz_property_graph(f; kw...))

function GraphvizGraphs.to_graphviz_property_graph(f::ACSetTransformation; kw...)
    pg = GraphvizGraphs.to_graphviz_property_graph(dom(f); kw...)
    vcolors = hex.(range(colorant"#0021A5", stop = colorant"#FA4616", length = nparts(codom(f), :V)))
    ecolors = hex.(range(colorant"#6C9AC3", stop = colorant"#E28F41", length = nparts(codom(f), :E)))
    hex.(colormap("Oranges", nparts(codom(f), :V)))
    for v in vertices(dom(f))
        fv = f[:V](v)
        set_vprops!(pg, v, Dict(:color => "#$(vcolors[fv])"))
    end
    for e in edges(dom(f))
        fe = f[:E](e)
        set_eprops!(pg, e, Dict(:color => "#$(ecolors[fe])"))
    end
    pg
end
include("autoplot.jl")
include("graph_bank.jl")
################################### Run the above code ###################################




# necessary structs

# struct SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}
# end



# struct BacktrackingState{S <: SchemaDescType,
#     Assign <: NamedTuple, PartialAssign <: NamedTuple,
#     Dom <: StructACSet{S}, Codom <: StructACSet{S}}
#   """ The current assignment, a partially-defined homomorphism of ACSets. """
#   assignment::Assign
#   """ Depth in search tree at which assignments were made. """
#   assignment_depth::Assign
#   """ Inverse assignment for monic components or if finding a monomorphism. """
#   inv_assignment::PartialAssign
#   """ Domain ACSet: the "variables" in the CSP. """
#   dom::Dom
#   """ Codomain ACSet: the "values" in the CSP. """
#   codom::Codom
# end







# homomorphisms
import Catlab.CategoricalAlgebra.CSets: homomorphisms
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components

# timers to profile functions
const to = TimerOutput()

# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    @timeit to "Homomorphism(): result initilialization" result = nothing
    @timeit to "Homomorphism(): homs calls" homomorphisms(X, Y; kw...) do α
      @timeit to "Homomorphism(): result assignment" result = α; return true
    end
    result
  end


# it uses two homomorphisms functions
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S};kw...) where {S}
    @timeit to "Homs(): results acset transformation" results = ACSetTransformation{S}[]
    homomorphisms(X, Y; kw...) do α
        @timeit to "Homs(): push" push!(results, map_components(deepcopy, α)); return false
    end
    results
end
@timeit to "Homs(): second homs function" homomorphisms(f, X::StructACSet, Y::StructACSet;monic=false, iso=false, initial=(;)) = @timeit to "Homs(): backtrack" backtracking_search(f, X, Y, monic=monic, iso=iso, initial=initial)


# determining which homs function the graphs use with homomorphism
function manyHom()
    h1 = homomorphism(line_two, directional_box)
    h2 = homomorphism(line_four, directional_box)
    h3 = homomorphism(line_six, directional_box)
    h4 = homomorphism(line_eight, directional_box)

    h1 = homomorphism(line_two, directional_2x2)
    h2 = homomorphism(line_four, directional_2x2)
    h3 = homomorphism(line_six, directional_2x2)
    h4 = homomorphism(line_eight, directional_2x2)

    h1 = homomorphism(a_sparse_from, a_sparse_to)
    h2 = homomorphism(a_sparse_to, a_sparse_from)
    h3 = homomorphism(a_sparse_from2, a_sparse_to2)
    h4 = homomorphism(a_sparse_to2, a_sparse_from2)

    h1 = homomorphism(a_sparse_from3, a_sparse_to3)
    h2 = homomorphism(a_sparse_to3, a_sparse_from3)
    h3 = homomorphism(a_sparse_from4, a_sparse_to4)
    h4 = homomorphism(a_sparse_to4, a_sparse_from4)
end
manyHom()
show(to)

# homs
function manyHoms()
    h1 = homomorphisms(line_two, directional_box)
    h2 = homomorphisms(line_four, directional_box)
    h3 = homomorphisms(line_six, directional_box)
    h4 = homomorphisms(line_eight, directional_box)

    h1 = homomorphisms(line_two, directional_2x2)
    h2 = homomorphisms(line_four, directional_2x2)
    h3 = homomorphisms(line_six, directional_2x2)
    h4 = homomorphisms(line_eight, directional_2x2)

    h1 = homomorphisms(a_sparse_from, a_sparse_to)
    h2 = homomorphisms(a_sparse_to, a_sparse_from)
    h3 = homomorphisms(a_sparse_from2, a_sparse_to2)
    h4 = homomorphisms(a_sparse_to2, a_sparse_from2)

    h1 = homomorphisms(a_sparse_from3, a_sparse_to3)
    h2 = homomorphisms(a_sparse_to3, a_sparse_from3)
    h3 = homomorphisms(a_sparse_from4, a_sparse_to4)
    h4 = homomorphisms(a_sparse_to4, a_sparse_from4)
end
manyHoms()

# The calling homomorphisms on two graphs appears to make calls to both
# homs functions equally. The homomorphism function between two graphs
# appears to call the second function exclusively.

# Unsurprisingly the backtracking_search function consumes almost the entirety
# of the function runtime. Further analysis on that will be conducted below.
show(to)



# Backtracking Search

# backtracking_search
import Catlab.Theories: SchemaDescType
import Catlab.CategoricalAlgebra.CSets: BacktrackingState
import Catlab.CategoricalAlgebra.CSets: find_mrv_elem, assign_elem!, unassign_elem!


const to = TimerOutput()
# necessary Structs


function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
    monic=false, iso=false, initial=(;)) where {Ob, S<:SchemaDescType{Ob}}
    # Fail early if no monic/isos exist on cardinality grounds.
    @timeit to "Backtrack1(): early failure" if iso isa Bool
        iso = iso ? Ob : ()
    end
    @timeit to "Backtrack1(): for c in iso" for c in iso
        nparts(X,c) == nparts(Y,c) || return false
    end
    @timeit to "Backtrack1(): if monic is bool" if monic isa Bool
        monic = monic ? Ob : ()
    end
    # Injections between finite sets are bijections, so reduce to that case.
    @timeit to "Backtrack1(): unique" monic = unique([iso..., monic...])
    @timeit to "Backtrack1(): for c in monic" for c in monic
        nparts(X,c) <= nparts(Y,c) || return false
    end

    # Initialize state variables for search.
    @timeit to "Backtrack1(): assignment init" assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
    @timeit to "Backtrack1(): assignment_depth init" assignment_depth = map(copy, assignment)
    @timeit to "Backtrack1(): inv_assignment init" inv_assignment = NamedTuple{Ob}(
        (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
        state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)

    # Make any initial assignments, failing immediately if inconsistent.
    @timeit to "Backtrack1(): initial assignments" for (c, c_assignments) in pairs(initial)
        for (x, y) in partial_assignments(c_assignments)
            assign_elem!(state, 0, Val{c}, x, y) || return false
        end
    end

    # Start the main recursion for backtracking search.
    @timeit to "Backtrack1(): recursion" backtracking_search(f, state, 1)
end

function backtracking_search(f, state::BacktrackingState, depth::Int)
    # Choose the next unassigned element.
    @timeit to "Backtrack2(): find_mrv_elem" mrv, mrv_elem = find_mrv_elem(state, depth)
    @timeit to "Backtrack2(): if isnothing" if isnothing(mrv_elem)
        # No unassigned elements remain, so we have a complete assignment.
        @timeit to "Backtrack2(): f(ACSetTransformation)" return f(ACSetTransformation(state.assignment, state.dom, state.codom))
    elseif mrv == 0
        # An element has no allowable assignment, so we must backtrack.
        return false
    end
    c, x = mrv_elem

    # Attempt all assignments of the chosen element.
    @timeit to "Backtrack2(): Y assignemnt" Y = state.codom
    @timeit to "Backtrack2(): for y in parts" for y in parts(Y, c)
        @timeit to "Backtrack2(): assign elem" assign_elem!(state, depth, Val{c}, x, y) &&
        @timeit to "Backtrack2(): recursion" backtracking_search(f, state, depth + 1) &&
            return true
            @timeit to "Backtrack2(): unassign_elem" unassign_elem!(state, depth, Val{c}, x)
    end
    return false
end


# The manyHom and manyHoms functions will make calls to the backtracking_search
manyHom()
show(to)
manyHoms()
show(to)