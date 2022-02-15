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

# homomorphisms imports
import Catlab.CategoricalAlgebra.CSets: homomorphisms
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components

# timers to profile functions
const to = TimerOutput()

# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    @timeit to "Homomorphism(): result initilialization" result = nothing
    @timeit to "Homomorphism(): homs calls" homomorphisms(X, Y; kw...) do α
        @timeit to "Homomorphism(): result assignment" result = α
        return true
    end
    result
end


# it uses two homomorphisms functions
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S}; kw...) where {S}
    @timeit to "Homs(): results acset transformation" results = ACSetTransformation{S}[]
    homomorphisms(X, Y; kw...) do α
        @timeit to "Homs(): push" push!(results, map_components(deepcopy, α))
        return false
    end
    results
end
@timeit to "Homs(): second homs function" homomorphisms(f, X::StructACSet, Y::StructACSet; monic = false, iso = false, initial = (;)) = @timeit to "Homs(): backtrack" backtracking_search(f, X, Y, monic = monic, iso = iso, initial = initial)


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

# backtracking_search imports
import Catlab.Theories: SchemaDescType
import Catlab.CategoricalAlgebra.CSets: BacktrackingState
import Catlab.CategoricalAlgebra.CSets: find_mrv_elem, assign_elem!, unassign_elem!





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
    @timeit to "Backtrack1(): unique" monic = unique([iso..., monic...])
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
    Y = state.codom
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

flattened_to = TimerOutputs.flatten(to)
show(flattened_to)

################################### Research/Reference Code ###################################
# Testing outputs for coloring homs

square = apex(product(u_line_two, add_loops(u_line_two)))
t1 = homomorphisms(square, u_line_two)
t2 = homomorphisms(u_line_two, square)

square = apex(product(u_line_four, add_loops(u_line_four)))
t1 = homomorphisms(square, u_line_four)
t2 = homomorphisms(u_line_four, square)

square = apex(product(u_line_three, add_loops(u_line_three)))
t1 = homomorphisms(square, u_line_three)
t2 = homomorphisms(u_line_three, square)

draw(t1[1])
draw(t1[2])
draw(t2[1])
draw(t2[2])

###############################################################################################


# Hom benchamrking with coloring sets
reset_timer!(to::TimerOutput)

# The following should produce acceptable results
# Squares
# 2-path
square = apex(product(u_line_two, add_loops(u_line_two)))
homomorphisms(u_line_two, square)
homomorphisms(u_line_three, square)
homomorphisms(u_line_four, square)
homomorphisms(u_line_five, square)
homomorphisms(u_line_six, square)
homomorphisms(u_line_seven, square)
homomorphisms(u_line_eight, square)

# 3-path
square = apex(product(u_line_three, add_loops(u_line_three)))
homomorphisms(u_line_two, square)
homomorphisms(u_line_three, square)
homomorphisms(u_line_four, square)
homomorphisms(u_line_five, square)
homomorphisms(u_line_six, square)
homomorphisms(u_line_seven, square)
homomorphisms(u_line_eight, square)

# 4-path
square = apex(product(u_line_four, add_loops(u_line_four)))
homomorphisms(u_line_two, square)
homomorphisms(u_line_three, square)
homomorphisms(u_line_four, square)
homomorphisms(u_line_five, square)
homomorphisms(u_line_six, square)
# Stopped here because doing more isn't possible (too large) - isues occur past here without a fresh start
# Anything beyond this point also takes a significant amount of time to complete
# homomorphisms(u_line_seven, square)
# homomorphisms(u_line_eight, square)

# 5-path
# square = apex(product(u_line_five, add_loops(u_line_five)))
# homomorphisms(u_line_two, square)
# homomorphisms(u_line_three, square)
# homomorphisms(u_line_four, square)
# homomorphisms(u_line_five, square)
# homomorphisms(u_line_six, square)
# homomorphisms(u_line_seven, square)
# homomorphisms(u_line_eight, square)

# 6-path
# square = apex(product(u_line_six, add_loops(u_line_six)))
# homomorphisms(u_line_two, square)
# homomorphisms(u_line_three, square)
# homomorphisms(u_line_four, square)
# homomorphisms(u_line_five, square)
# homomorphisms(u_line_six, square)
# homomorphisms(u_line_seven, square)
# homomorphisms(u_line_eight, square)

# 7-path
# square = apex(product(u_line_seven, add_loops(u_line_seven)))
# homomorphisms(u_line_two, square)
# homomorphisms(u_line_three, square)
# homomorphisms(u_line_four, square)
# homomorphisms(u_line_five, square)
# homomorphisms(u_line_six, square)
# homomorphisms(u_line_seven, square)
# homomorphisms(u_line_eight, square)

# 8-path
# square = apex(product(u_line_eight, add_loops(u_line_eight)))
# homomorphisms(u_line_two, square)
# homomorphisms(u_line_three, square)
# homomorphisms(u_line_four, square)
# homomorphisms(u_line_five, square)
# homomorphisms(u_line_six, square)
# homomorphisms(u_line_seven, square)
# homomorphisms(u_line_eight, square)

show(to)
flattened_to = TimerOutputs.flatten(to)
show(flattened_to)
# The results aren't too surprising. Recursion take up the majority of the time and memory
# used by the backtracking_search.

# Unsure about these, but the hom performance remains
reset_timer!(to::TimerOutput)
# 2-path
square = apex(product(u_line_two, add_loops(u_line_two)))
homomorphisms(square, u_line_two)
homomorphisms(square, u_line_three)
homomorphisms(square, u_line_four)
homomorphisms(square, u_line_five)
homomorphisms(square, u_line_six)
homomorphisms(square, u_line_seven)
homomorphisms(square, u_line_eight)

# 3-path
square = apex(product(u_line_three, add_loops(u_line_three)))
homomorphisms(square, u_line_two)
homomorphisms(square, u_line_three)
homomorphisms(square, u_line_four)
homomorphisms(square, u_line_five)
homomorphisms(square, u_line_six)
homomorphisms(square, u_line_seven)
homomorphisms(square, u_line_eight)

# 4-path
square = apex(product(u_line_four, add_loops(u_line_four)))
homomorphisms(square, u_line_two)
homomorphisms(square, u_line_three)
homomorphisms(square, u_line_four)
homomorphisms(square, u_line_five)
homomorphisms(square, u_line_six)

show(to)
flattened_to = TimerOutputs.flatten(to)
show(flattened_to)

# Performance is about the same in both directions.

# G smaller than H (Acyclic)
reset_timer!(to::TimerOutput)

homomorphisms(a_sparse_from, a_sparse_to)
homomorphisms(a_sparse_from2, a_sparse_to2)
homomorphisms(a_sparse_from3, a_sparse_to3)
homomorphisms(a_sparse_from4, a_sparse_to4)
homomorphisms(a_sparse_from5, a_sparse_to5)

homomorphisms(a_sparse_from, a_sparse_to2)
homomorphisms(a_sparse_from, a_sparse_to4)
homomorphisms(a_sparse_from, a_sparse_to5)

homomorphisms(a_sparse_from2, a_sparse_to)
homomorphisms(a_sparse_from2, a_sparse_to4)
homomorphisms(a_sparse_from2, a_sparse_to5)
homomorphisms(a_sparse_from2, a_sparse_from4)
homomorphisms(a_sparse_from2, a_sparse_from5)

homomorphisms(a_sparse_from3, a_sparse_to)
homomorphisms(a_sparse_from3, a_sparse_to2)
homomorphisms(a_sparse_from3, a_sparse_to4)
homomorphisms(a_sparse_from3, a_sparse_to5)
homomorphisms(a_sparse_from3, a_sparse_from)
homomorphisms(a_sparse_from3, a_sparse_from4)
homomorphisms(a_sparse_from3, a_sparse_from5)

show(to)
flattened_to = TimerOutputs.flatten(to)
show(flattened_to)

# G larger than H (Acyclic)
reset_timer!(to::TimerOutput)

homomorphisms(a_sparse_to, a_sparse_from)
homomorphisms(a_sparse_to2, a_sparse_from2)
homomorphisms(a_sparse_to3, a_sparse_from3)
homomorphisms(a_sparse_to4, a_sparse_from4)
homomorphisms(a_sparse_to5, a_sparse_from5)

homomorphisms(a_sparse_to2, a_sparse_from)
homomorphisms(a_sparse_to4, a_sparse_from)
homomorphisms(a_sparse_to5, a_sparse_from)

homomorphisms(a_sparse_to, a_sparse_from2)
homomorphisms(a_sparse_to4, a_sparse_from2)
homomorphisms(a_sparse_to5, a_sparse_from2)
homomorphisms(a_sparse_from4, a_sparse_from2)
homomorphisms(a_sparse_from5, a_sparse_from2)

homomorphisms(a_sparse_to, a_sparse_from3)
homomorphisms(a_sparse_to2, a_sparse_from3)
homomorphisms(a_sparse_to4, a_sparse_from3)
homomorphisms(a_sparse_to5, a_sparse_from3)
homomorphisms(a_sparse_from, a_sparse_from3)
homomorphisms(a_sparse_from4, a_sparse_from3)
homomorphisms(a_sparse_from5, a_sparse_from3)

show(to)
flattened_to = TimerOutputs.flatten(to)
show(flattened_to)

# G about the same size as H
reset_timer!(to::TimerOutput)

homomorphisms(a_sparse_to, a_sparse_to5)
homomorphisms(a_sparse_to5, a_sparse_to)

homomorphisms(a_sparse_from, a_sparse_to3)
homomorphisms(a_sparse_to3, a_sparse_from)
# homomorphisms(a_sparse_from, a_complete_from)
# homomorphisms(a_complete_from, a_sparse_from)
# homomorphisms(a_sparse_to3, a_complete_from)
# homomorphisms(a_complete_from, a_sparse_to3)

homomorphisms(a_sparse_from5, a_sparse_to2)
homomorphisms(a_sparse_to2, a_sparse_from5)

show(to)
flattened_to = TimerOutputs.flatten(to)
show(flattened_to)