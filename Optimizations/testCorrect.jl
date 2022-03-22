include("Correct.jl")
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
gtoh = compareFunctions(g, h_codom)

large1 = apex(product(a_sparse_three, a_sparse_four))
large2 = apex(product(a_sparse_four, a_sparse_five))
large3 = apex(product(a_sparse_five, a_sparse_six))
large4 = apex(product(a_sparse_six, a_sparse_six2))
large5 = apex(product(a_sparse_six2, a_sparse_seven))
large6 = apex(product(a_sparse_seven, a_sparse_eight))
large7 = apex(product(a_sparse_eight, a_sparse_eight2))

compareFunctions(large1, a_sparse_five)
compareFunctions(large2, a_sparse_three)
compareFunctions(large3, a_sparse_seven)
compareFunctions(large4, a_sparse_eight)
draw(h)

compareFunctions(large5, large2)
compareFunctions(large6, large3)
compareFunctions(large7, large4)
compareFunctions(large1, a_sparse_three)
compareFunctions(large2, a_sparse_six)
compareFunctions(large3, a_sparse_eight)
compareFunctions(large4, large1) # THIS ONE BREAKS - When looking at it the values are wrong for the depth
compareFunctions(large5, large3)
compareFunctions(a_sparse_eight, a_sparse_seven)
compareFunctions(a_sparse_eight2, a_sparse_six)
compareFunctions(a_sparse_five, a_sparse_three)
compareFunctions(a_sparse_six2, a_sparse_four)
