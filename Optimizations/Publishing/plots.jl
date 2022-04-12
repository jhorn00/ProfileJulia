include("./Support/graph_bank.jl")
include("./Support/autoPlot.jl")

fromGraphs = [a_sparse_three, a_sparse_four, a_sparse_five, a_sparse_six, a_sparse_seven, a_sparse_eight, a_sparse_five]
toGraphs = [a_sparse_seven, a_sparse_eight, a_sparse_six, a_sparse_five, a_sparse_three, a_sparse_four, a_sparse_eight2]
for i in 1:10
    autoGens(fromGraphs, toGraphs, 20, 200)
end
autoShuffle(fromGraphs, toGraphs, 20, 200)
# autoShuffle(fromGraphs, toGraphs, 20, 50)
# autoGen(fromGraphs, 20, 50)
fromGraphs
toGraphs
BenchmarkTools.DEFAULT_PARAMETERS.samples = 1000

if length(fromGraphs) != length(toGraphs)
    println("From and to lists should be the same size.")
    return
end
println("Autoplotting Homs...\nTotal pairs: $(length(toGraphs))")
x1 = Int64[]
y1 = Float64[]
for i in 1:length(fromGraphs)
    print("Graph pair $i\n")
    f = fromGraphs[i]
    t = toGraphs[i]
    append!(y1, time(median(@benchmark homomorphism($f, add_loops($t)))))
    append!(x1, length(vertices(f)))
end
scatter([x1], [y1], title="Autoplotted Graph Vertices", xlabel="Number of \"From\" Vertices", ylabel="Single Hom Calculation Time (ns)")
savefig("autoVertex.png")

# Checkerboard to Path - BenchmarkTools
x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:5
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(component)
        checkH = @benchmark homomorphism($checkerboard, $codom)
        for_x = Array{Int64,1}(undef, length(checkH.times))
        fill!(for_x, n)
        append!(x, for_x)
        append!(y, checkH.times / 1000000000)
        # codom = add_loops(checkerboard)
        # checkH = @benchmark homomorphism($component, $codom)
        # for_x = Array{Int64,1}(undef, length(checkH.times))
        # fill!(for_x, n)
        # append!(x, for_x)
        # append!(y, checkH.times / 1000000)
    end
end
scatter([x], [y], title="Homomorphism Function (BenchmarkTools)", xlabel="Graph Dimensions (Path Graph Vertex count)", ylabel="Single Hom Calculation Time (seconds)", legend=false)
savefig("HomGenPerformance.png")
length(x)
length(y)

using TimerOutputs
const to = TimerOutput()
reset_timer!(to::TimerOutput)
x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:50
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(component)
        reset_timer!(to::TimerOutput)
        @timeit to "homomorphism" homomorphism(checkerboard, codom)
        append!(x, n)
        append!(y, TimerOutputs.time(to["homomorphism"]) / 1000000000)
        # codom = add_loops(checkerboard)
        # checkH = @benchmark homomorphism($component, $codom)
        # for_x = Array{Int64,1}(undef, length(checkH.times))
        # fill!(for_x, n)
        # append!(x, for_x)
        # append!(y, checkH.times / 1000000)
    end
end
scatter([x], [y], title="Homomorphism Function (TimerOutputs)", xlabel="Graph Dimensions (Path Graph Vertex count)", ylabel="Single Hom Calculation Time (seconds)", legend=false)
savefig("HomGenPerformanceTO.png")

include("../../Includes/iterativeBoilerplate.jl")
import Catlab.CategoricalAlgebra.CSets: attr, adom, acodom, out_hom, quot

""" Internal state for backtracking search for ACSet homomorphisms.
"""
mutable struct IterativeBacktrackingState
    # needed to resume
    x::Int64
    iterator::Base.Iterators.Stateful{UnitRange{Int64},Union{Nothing,Tuple{Int64,Int64}}}
end

ihomomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
    ihomomorphism(X, Y, alg; kw...)

function ihomomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
    result = nothing
    iterative_backtracking_search(X, Y; kw...) do α
        result = α
        return true
    end
    result
end

ihomomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
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
    @timeit to "iterative backtracking_search" iterative_backtracking_search(f, state)
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
            # I believe the time taken to run assign_elem is deceptively small.
            # find_mrv_elem, which takes the bulk of the process resources, makes multiple calls to it.
            # Therefore, speeding it up should give much better performance.
            t = assign_elem!(state, depth, Val{c}, currentState.x, y)
            if t
                # && return true
                depth = depth + 1
                mrv, mrv_elem = find_mrv_elem(state, depth)
                # see if we can store these to run the function less - not possible
                # println("mrv: ", mrv)
                # println("mrv_elem: ", mrv)
                # println("depth: ", depth)
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

using DataStructures

""" Internal state for backtracking search for ACSet homomorphisms.
"""
mutable struct IterativeBacktrackingState
    # needed to resume
    x::Int64
    iterator::Base.Iterators.Stateful{UnitRange{Int64},Union{Nothing,Tuple{Int64,Int64}}}
end

# Checkerboard to Path - BenchmarkTools
x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:5
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(component)
        checkH = @benchmark ihomomorphism($checkerboard, $codom)
        for_x = Array{Int64,1}(undef, length(checkH.times))
        fill!(for_x, n)
        append!(x, for_x)
        append!(y, checkH.times / 1000000000)
        # codom = add_loops(checkerboard)
        # checkH = @benchmark homomorphism($component, $codom)
        # for_x = Array{Int64,1}(undef, length(checkH.times))
        # fill!(for_x, n)
        # append!(x, for_x)
        # append!(y, checkH.times / 1000000)
    end
end
scatter([x], [y], title="Iterative Homomorphism Function (BenchmarkTools)", xlabel="Graph Dimensions (Path Graph Vertex count)", ylabel="Single Hom Calculation Time (seconds)", legend=false)
savefig("HomGenPerformanceIt.png")
length(x)
length(y)

reset_timer!(to::TimerOutput)
x = Int64[]
y = Float64[]
for n in 1:20
    for j in 1:50
        println(n)
        component = path_graph(ReflexiveGraph, n)
        checkerboard = box_product(component, component)
        codom = add_loops(component)
        reset_timer!(to::TimerOutput)
        @timeit to "homomorphism" ihomomorphism(checkerboard, codom)
        append!(x, n)
        append!(y, TimerOutputs.time(to["homomorphism"]) / 1000000000)
        # codom = add_loops(checkerboard)
        # checkH = @benchmark homomorphism($component, $codom)
        # for_x = Array{Int64,1}(undef, length(checkH.times))
        # fill!(for_x, n)
        # append!(x, for_x)
        # append!(y, checkH.times / 1000000)
    end
end
scatter([x], [y], title="Iterative Homomorphism Function (TimerOutputs)", xlabel="Graph Dimensions (Path Graph Vertex count)", ylabel="Single Hom Calculation Time (seconds)", legend=false)
savefig("HomGenPerformanceTOIt.png")