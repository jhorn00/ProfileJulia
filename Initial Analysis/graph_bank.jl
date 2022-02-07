using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs

# Acyclic Sparse
a_sparse_from = @acset Graphs.Graph begin
    V = 4
    E = 4
    src = [1, 1, 2, 3]
    tgt = [2, 3, 4, 4]
end

a_sparse_to = @acset Graphs.Graph begin
    V = 8
    E = 8
    src = [1, 2, 2, 3, 4, 6, 7, 8]
    tgt = [2, 3, 5, 7, 2, 4, 8, 5]
end

a_sparse_from2 = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 1, 2]
    tgt = [2, 3, 3]
end

a_sparse_to2 = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [1, 2, 3, 5, 6, 6]
    tgt = [2, 3, 5, 4, 3, 5]
end

a_sparse_from3 = @acset Graphs.Graph begin
    V = 2
    E = 1
    src = [1]
    tgt = [2]
end

a_sparse_to3 = @acset Graphs.Graph begin
    V = 4
    E = 3
    src = [1, 2, 3]
    tgt = [2, 3, 4]
end

a_sparse_from4 = @acset Graphs.Graph begin
    V = 5
    E = 5
    src = [1, 1, 2, 3, 4]
    tgt = [3, 5, 5, 5, 5]
end

a_sparse_to4 = @acset Graphs.Graph begin
    V = 7
    E = 7
    src = [1, 3, 4, 5, 6, 6, 7]
    tgt = [4, 1, 2, 3, 3, 4, 2]
end

a_sparse_from5 = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [3, 2, 2, 1, 4, 5]
    tgt = [2, 1, 4, 5, 6, 6]
end

a_sparse_to5 = @acset Graphs.Graph begin
    V = 8
    E = 8
    src = [1, 1, 2, 3, 3, 3, 4, 4]
    tgt = [3, 4, 4, 2, 7, 8, 5, 6]
end

# Acyclic Complete - Edge from each vertex to all vertices that do not form loops.
a_complete_from = @acset Graphs.Graph begin
    V = 4
    E = 6
    src = [1, 1, 1, 2, 2, 3]
    tgt = [2, 3, 4, 3, 4, 4]
end

a_complete_to = @acset Graphs.Graph begin
    V = 6
    E = 15
    src = [1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5]
    tgt = [2, 3, 4, 5, 6, 3, 4, 5, 6, 4, 5, 6, 5, 6, 6]
end