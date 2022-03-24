using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
using TimerOutputs
draw(g) = to_graphviz(g, node_labels=true, edge_labels=true)
GraphvizGraphs.to_graphviz(f::ACSetTransformation; kw...) =
    to_graphviz(GraphvizGraphs.to_graphviz_property_graph(f; kw...))

function GraphvizGraphs.to_graphviz_property_graph(f::ACSetTransformation; kw...)
    pg = GraphvizGraphs.to_graphviz_property_graph(dom(f); kw...)
    vcolors = hex.(range(colorant"#0021A5", stop=colorant"#FA4616", length=nparts(codom(f), :V)))
    ecolors = hex.(range(colorant"#6C9AC3", stop=colorant"#E28F41", length=nparts(codom(f), :E)))
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
include("../../Includes/graph_bank.jl")
include("../../Includes/autoplot.jl")

# homomorphisms imports
import Catlab.CategoricalAlgebra.CSets: homomorphisms, homomorphism
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components

# backtracking_search imports
import Catlab.Theories: SchemaDescType
import Catlab.CategoricalAlgebra.CSets: BacktrackingState, find_mrv_elem, can_assign_elem, quot
import Catlab.CategoricalAlgebra.CSets: find_mrv_elem, assign_elem!, unassign_elem!, out_attr, out_hom

numSamples = 500
BenchmarkTools.DEFAULT_PARAMETERS.samples = numSamples

################################### Run the above code ###################################

const to = TimerOutput()

# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    result = nothing
    @timeit to "homomorphisms() call" homomorphisms(X, Y; kw...) do α
        result = α
        return true
    end
    result
end


# it uses two homomorphisms functions
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S}; kw...) where {S}
    results = ACSetTransformation{S}[]
    @timeit to "recursive homomorphisms() call" homomorphisms(X, Y; kw...) do α
        push!(results, map_components(deepcopy, α))
        return false
    end
    results
end
homomorphisms(f, X::StructACSet, Y::StructACSet; monic=false, iso=false, initial=(;)) = @timeit to "backtracking() call" backtracking_search(f, X, Y, monic=monic, iso=iso, initial=initial)

# Backtracking
# function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
#     monic = false, iso = false, initial = (;)) where {Ob,S<:SchemaDescType{Ob}}
#     # Fail early if no monic/isos exist on cardinality grounds.
#     if iso isa Bool
#         iso = iso ? Ob : ()
#     end
#     @timeit to "for c in iso" for c in iso
#         nparts(X, c) == nparts(Y, c) || return false
#     end

#     if monic isa Bool
#         monic = monic ? Ob : ()
#     end
#     # Injections between finite sets are bijections, so reduce to that case.
#     @timeit to "unique() call" monic = unique([iso..., monic...])
#     @timeit to "for c in iso" for c in monic
#         nparts(X, c) <= nparts(Y, c) || return false
#     end
#     # Initialize state variables for search.
#     @timeit to "assignment" assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
#     @timeit to "assignment_depth" assignment_depth = map(copy, assignment)
#     @timeit to "inv_assignment" inv_assignment = NamedTuple{Ob}(
#         (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
#     @timeit to "BacktrackingState" state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)
#     # Make any initial assignments, failing immediately if inconsistent.
#     @timeit to "for (c, c_assignments) in pairs" for (c, c_assignments) in pairs(initial)
#         @timeit to "for(x, y) in partial_assignments" for (x, y) in partial_assignments(c_assignments)
#             assign_elem!(state, 0, Val{c}, x, y) || return false
#         end
#     end
#     # Start the main recursion for backtracking search.
#     @timeit to "Start backtrack recursion" backtracking_search(f, state, 1)
# end

# function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
#     monic = false, iso = false, initial = (;)) where {Ob,S<:SchemaDescType{Ob}}
#     # Fail early if no monic/isos exist on cardinality grounds.
#     if iso isa Bool
#         iso = iso ? Ob : ()
#     end
#     for c in iso
#         nparts(X, c) == nparts(Y, c) || return false
#     end

#     if monic isa Bool
#         monic = monic ? Ob : ()
#     end
#     # Injections between finite sets are bijections, so reduce to that case.
#     monic = unique([iso..., monic...])
#     for c in monic
#         nparts(X, c) <= nparts(Y, c) || return false
#     end
#     # Initialize state variables for search.
#     assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
#     assignment_depth = map(copy, assignment)
#     inv_assignment = NamedTuple{Ob}(
#         (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
#     state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)
#     # Make any initial assignments, failing immediately if inconsistent.
#     for (c, c_assignments) in pairs(initial)
#         for (x, y) in partial_assignments(c_assignments)
#             assign_elem!(state, 0, Val{c}, x, y) || return false
#         end
#     end
#     # Start the main recursion for backtracking search.
#     @timeit to "Start backtrack recursion" backtracking_search(f, state, 1)
# end

# # Recursive backtracking_search function
# function backtracking_search(f, state::BacktrackingState, depth::Int)
#     # Choose the next unassigned element.
#     mrv, mrv_elem = @timeit to "find_mrv_elem" find_mrv_elem(state, depth)
#     if isnothing(mrv_elem)
#         # No unassigned elements remain, so we have a complete assignment.
#         return f(ACSetTransformation(state.assignment, state.dom, state.codom))
#     elseif mrv == 0
#         # An element has no allowable assignment, so we must backtrack.
#         return false
#     end
#     c, x = mrv_elem
#     # Attempt all assignments of the chosen element.
#     Y = state.codom
#     for y in parts(Y, c)
#         @timeit to "assign_elem" assign_elem!(state, depth, Val{c}, x, y) &&
#                                  @timeit to "backtracking recursive call" backtracking_search(f, state, depth + 1) &&
#                                                                           return true
#         unassign_elem!(state, depth, Val{c}, x)
#     end
#     return false
# end

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

# Recursive backtracking_search function
function backtracking_search(f, state::BacktrackingState, depth::Int)
    # if depth == 15
    #     return true
    # end
    println("runs")
    # Choose the next unassigned element.
    mrv, mrv_elem = find_mrv_elem(state, depth)
    # println("mrv: ", mrv)
    if isnothing(mrv_elem)
        println("isnothing")
        # No unassigned elements remain, so we have a complete assignment.
        return f(ACSetTransformation(state.assignment, state.dom, state.codom))
    elseif mrv == 0
        println("mrv == 0")
        # An element has no allowable assignment, so we must backtrack.
        return false
    end
    c, x = mrv_elem
    # Attempt all assignments of the chosen element.
    Y = state.codom
    for y in parts(Y, c)
        println("y: ", y)
        println("x: ", x)
        println("depth: ", depth)
        if y == 1
            println(state.assignment)
        end
        # println(state.assignment.V)
        # println(state.assignment.E)
        # println("length p: ", parts(Y, c))
        # if depth == 16
        #     println("State:\n", state, "\n")
        #     println("depth:\n", depth, "\n")
        #     println("Val{c}:\n", Val{c}, "\n")
        #     println("x:\n", x, "\n")
        #     println("y:\n", y, "\n")
        # end
        # println("c: ", c, " x: ", x)
        # println("currentState.c: ", c, " currentState.x: ", x)

        t = assign_elem!(state, depth, Val{c}, x, y)

        if (depth == 12 && (y == 6 || y == 7 || y == 8 || y == 9)) || (depth == 13 && y == 1)
            println("assign_elem: ", t)
            println("state: ", state)
            println("depth: ", depth)
            println("Val: ", Val{c})
            println("x: ", x)
            println("y: ", y)
        end
        # println(state.assignment)
        if t
            println("assign_elem")
            if backtracking_search(f, state, depth + 1)
                println("ret is true")
                return true
            end
        end
        unassign_elem!(state, depth, Val{c}, x)
        println("unassign_elem")
        println(x)
        println(depth)
    end
    return false
end


""" Find an unassigned element having the minimum remaining values (MRV).
"""
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


@generated function assign_elem!(state::BacktrackingState{S}, depth,
    ::Type{Val{c}}, x, y) where {S,c}
    quote
        y′ = state.assignment.$c[x]
        y′ == y && return true  # If x is already assigned to y, return immediately.
        y′ == 0 || return false # Otherwise, x must be unassigned.
        @timeit to "if" if !isnothing(state.inv_assignment.$c) && state.inv_assignment.$c[y] != 0
            # Also, y must unassigned in the inverse assignment.
            return false
        end

        # Check attributes first to fail as quickly as possible.
        X, Y = state.dom, state.codom
        $(map(@timeit to "out_attr" out_attr(S, c)) do f
            :(@timeit to "subpart 1" subpart(X, x, $(@timeit to "quot 1" quot(f))) == @timeit to "subpart 2" subpart(Y, y, $(@timeit to "quot 2" quot(f))) || return false)
        end...)

        # Make the assignment and recursively assign subparts.
        state.assignment.$c[x] = y
        state.assignment_depth.$c[x] = depth
        @timeit to "if 2" if !isnothing(state.inv_assignment.$c)
            state.inv_assignment.$c[y] = x
        end
        $(map(@timeit to "out_hom" out_hom(S, c)) do (f, d)
            :(assign_elem!(state, depth, Val{$(quot(d))}, subpart(X, x, $(quot(f))),
                subpart(Y, y, $(quot(f)))) || return false)
        end...)
        return true
    end
end


# Checkerboard surjection - BenchmarkTools
# x = Int64[]
# y = Float64[]
# for n in 1:20
#     for j in 1:3
#         println(n)
#         component = path_graph(ReflexiveGraph, n)
#         checkerboard = box_product(component, component)
#         codom = add_loops(component)
#         checkH = @benchmark homomorphism($checkerboard, $codom)
#         for_x = Array{Int64,1}(undef, length(checkH.times))
#         fill!(for_x, n)
#         append!(x, for_x)
#         append!(y, checkH.times)
#     end
# end
# scatter([x], [y], title = "Homomorphism Function", xlabel = "Graph Dimensions (Path Graph Vertex count)", ylabel = "Single Hom Calculation Time (ns)")
# savefig("tempSur.png")
# length(x)
# length(y)

# Checkerboard injection - BenchmarkTools


# x = Int64[]
# y = Float64[]
# for n in 1:20
#     for j in 1:3
#         println(n)
#         component = path_graph(ReflexiveGraph, n)
#         checkerboard = box_product(component, component)
#         codom = add_loops(checkerboard)
#         checkH = @benchmark homomorphism($component, $codom)
#         for_x = Array{Int64,1}(undef, length(checkH.times))
#         fill!(for_x, n)
#         append!(x, for_x)
#         append!(y, checkH.times)
#     end
# end
# scatter([x], [y], title = "Homomorphism Function", xlabel = "Graph Dimensions (Path Graph Vertex count)", ylabel = "Single Hom Calculation Time (ns)")
# savefig("tempInj.png")
# length(x)
# length(y)



# after this go in and run the same datasets but with benchmarking being called on inside functions
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
gtoh = homomorphism(g, h_codom)

large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

homomorphism(large1, add_loops(a_sparse_five))
homomorphism(large2, add_loops(a_sparse_three))
homomorphism(large3, add_loops(a_sparse_seven))
h = homomorphism(large4, add_loops(a_sparse_eight))
draw(h)
homomorphism(large5, add_loops(large2))
homomorphism(large6, add_loops(large3))
homomorphism(large7, add_loops(large4))
homomorphism(large1, add_loops(a_sparse_three))
homomorphism(large2, add_loops(a_sparse_six))
homomorphism(large3, add_loops(a_sparse_eight))
homomorphism(large4, add_loops(large1)) #this one
homomorphism(large5, add_loops(large3))
homomorphism(a_sparse_eight, add_loops(a_sparse_seven))
homomorphism(a_sparse_eight2, add_loops(a_sparse_six))
homomorphism(a_sparse_five, add_loops(a_sparse_three))
homomorphism(a_sparse_six2, add_loops(a_sparse_four))


reset_timer!(to::TimerOutput)
component = path_graph(ReflexiveGraph, 2)
checkerboard = box_product(component, component)
codom = add_loops(component)
checkH = homomorphism(checkerboard, codom)
# component = path_graph(ReflexiveGraph, 3)
# checkerboard = box_product(component, component)
# codom = add_loops(component)
# checkH = homomorphism(checkerboard, codom)
# component = path_graph(ReflexiveGraph, 4)
# checkerboard = box_product(component, component)
# codom = add_loops(component)
# checkH = homomorphism(checkerboard, codom)
show(to)
show(TimerOutputs.flatten(to))

################### GRIDS ###################

reset_timer!(to::TimerOutput)
for n in 1:15 # number of vertices ranges from 1 to 20
    for j in 1:3 # runs each 3 times
        println(n)
        component = path_graph(ReflexiveGraph, n) # generate path graph of size n
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(component) # add loops to the codomain
        checkH = homomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***
    end
end
show(TimerOutputs.flatten(to))

reset_timer!(to::TimerOutput)
for n in 1:8 # number of vertices ranges from 1 to 20
    for j in 1:3 # runs each 3 times
        println(n)
        component = path_graph(ReflexiveGraph, n) # generate path graph of size n
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(checkerboard) # add loops to the codomain
        checkH = homomorphism(component, codom) # generate homomorphism ***PATH -> GRID***
    end
end
show(TimerOutputs.flatten(to))

################### G larger than H for G->H ###################

large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

reset_timer!(to::TimerOutput)
for i in 1:3
    homomorphism(large1, add_loops(a_sparse_five))
    homomorphism(large2, add_loops(a_sparse_three))
    homomorphism(large3, add_loops(a_sparse_seven))
    homomorphism(large4, add_loops(a_sparse_eight))
    homomorphism(large5, add_loops(large2))
    homomorphism(large6, add_loops(large3))
    homomorphism(large7, add_loops(large4))
    homomorphism(large1, add_loops(a_sparse_three))
    homomorphism(large2, add_loops(a_sparse_six))
    homomorphism(large3, add_loops(a_sparse_eight))
    homomorphism(large4, add_loops(large1))
    homomorphism(large5, add_loops(large3))
    homomorphism(a_sparse_eight, add_loops(a_sparse_seven))
    homomorphism(a_sparse_eight2, add_loops(a_sparse_six))
    homomorphism(a_sparse_five, add_loops(a_sparse_three))
    homomorphism(a_sparse_six2, add_loops(a_sparse_four))
end
show(to)
show(TimerOutputs.flatten(to))

################### H larger than G  for G->H ###################

reset_timer!(to::TimerOutput)
homomorphism(a_sparse_three, add_loops(large1))
homomorphism(a_sparse_six, add_loops(large2))
homomorphism(a_sparse_eight, add_loops(large3))
homomorphism(a_sparse_five, add_loops(large1))
homomorphism(a_sparse_three, add_loops(large2))
homomorphism(a_sparse_seven, add_loops(large3))
homomorphism(a_sparse_eight, add_loops(large4))
show(to)

for i in 1:3
    homomorphism(a_sparse_five, add_loops(large1))
    homomorphism(a_sparse_three, add_loops(large2))
    homomorphism(a_sparse_seven, add_loops(large3))
    homomorphism(a_sparse_eight, add_loops(large4))
    homomorphism(large2, add_loops(large5))
    homomorphism(large3, add_loops(large6))
    homomorphism(large4, add_loops(large7))
    homomorphism(a_sparse_three, add_loops(large1))
    homomorphism(a_sparse_six, add_loops(large2))
    homomorphism(a_sparse_eight, add_loops(large3))
    homomorphism(large1, add_loops(large4))
    homomorphism(large3, add_loops(large5))
    homomorphism(a_sparse_seven, add_loops(a_sparse_eight))
    homomorphism(a_sparse_six, add_loops(a_sparse_eight2))
    homomorphism(a_sparse_three, add_loops(a_sparse_five))
    homomorphism(a_sparse_four, add_loops(a_sparse_six2))
end
show(to)
show(TimerOutputs.flatten(to))

# G about the same size as H
reset_timer!(to::TimerOutput)

for i in 1:3
    # same
    homomorphism(a_sparse_five, add_loops(a_sparse_five))
    homomorphism(a_sparse_eight, add_loops(a_sparse_eight))
    homomorphism(a_sparse_seven, add_loops(a_sparse_eight2))
    homomorphism(a_sparse_eight, add_loops(a_sparse_seven))
    homomorphism(a_sparse_three, add_loops(a_sparse_four))
    homomorphism(a_sparse_six, add_loops(a_sparse_five))
    homomorphism(a_sparse_four, add_loops(a_sparse_five))
    homomorphism(a_sparse_five, add_loops(a_sparse_four))
    homomorphism(a_sparse_four, add_loops(a_sparse_three))
    homomorphism(a_sparse_seven, add_loops(a_sparse_eight))
    homomorphism(a_sparse_six, add_loops(a_sparse_six2))
    homomorphism(a_sparse_six2, add_loops(a_sparse_five))
    homomorphism(a_sparse_five, add_loops(a_sparse_six2))
end
show(to)
show(TimerOutputs.flatten(to))

# after that let's look into the functions that are called a good bit as well as what the hom function is exploring