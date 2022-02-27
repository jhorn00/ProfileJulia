using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
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
include("graph_bank.jl")
include("autoplot.jl")

# homomorphisms imports
import Catlab.CategoricalAlgebra.CSets: homomorphisms, homomorphism
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components

# backtracking_search imports
import Catlab.Theories: SchemaDescType
import Catlab.CategoricalAlgebra.CSets: BacktrackingState
import Catlab.CategoricalAlgebra.CSets: find_mrv_elem, assign_elem!, unassign_elem!

################################### Run the above code ###################################



# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    result = nothing
    homomorphisms(X, Y; kw...) do α
        result = α
        return true
    end
    result
end


# it uses two homomorphisms functions
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S}; kw...) where {S}
    results = ACSetTransformation{S}[]
    homomorphisms(X, Y; kw...) do α
        push!(results, map_components(deepcopy, α))
        return false
    end
    results
end
homomorphisms(f, X::StructACSet, Y::StructACSet; monic = false, iso = false, initial = (;)) = backtracking_search(f, X, Y, monic = monic, iso = iso, initial = initial)

# Backtracking

function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
    monic = false, iso = false, initial = (;)) where {Ob,S<:SchemaDescType{Ob}}
    # Fail early if no monic/isos exist on cardinality grounds.
    ### rarely called, takes no time/resources
    if iso isa Bool
        iso = iso ? Ob : ()
    end
    ### rarely called, takes no time/resources
    for c in iso
        nparts(X, c) == nparts(Y, c) || return false
    end
    ### rarely called, takes no time/resources
    if monic isa Bool
        monic = monic ? Ob : ()
    end
    # Injections between finite sets are bijections, so reduce to that case.
    monic = unique([iso..., monic...])
    ### rarely called, takes no time/resources
    for c in monic
        nparts(X, c) <= nparts(Y, c) || return false
    end

    # Initialize state variables for search.
    ### rarely called, takes no time/resources
    assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
    ### rarely called, takes no time/resources
    assignment_depth = map(copy, assignment)
    ### rarely called, takes no time/resources
    inv_assignment = NamedTuple{Ob}(
        (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
    state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)

    # Make any initial assignments, failing immediately if inconsistent.
    ### rarely called, takes no time/resources
    for (c, c_assignments) in pairs(initial)
        for (x, y) in partial_assignments(c_assignments)
            assign_elem!(state, 0, Val{c}, x, y) || return false
        end
    end

    # Start the main recursion for backtracking search.
    backtracking_search(f, state, 1)
end

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

################### GRIDS ###################

for n in 1:15 # number of vertices ranges from 1 to 15
    for j in 1:3 # runs each 3 times
        println(n)
        component = path_graph(ReflexiveGraph, n) # generate path graph of size n
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom_val = add_loops(component) # add loops to the codomain
        checkH = @btime homomorphism($checkerboard, $codom_val) # generate homomorphism ***GRID -> PATH***
    end
end

for n in 1:15 # number of vertices ranges from 1 to 15
    for j in 1:3 # runs each 3 times
        println(n)
        component = path_graph(ReflexiveGraph, n) # generate path graph of size n
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom_val = add_loops(checkerboard) # add loops to the codomain
        checkH = @btime homomorphism($component, $codom_val) # generate homomorphism ***PATH -> GRID***
    end
end