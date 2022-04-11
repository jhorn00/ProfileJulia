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