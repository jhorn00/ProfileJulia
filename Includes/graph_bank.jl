using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs

# Acyclic Sparse V ≈ E or V = E
# Arranged in increasing vertex count.
# Naming scheme is based on vertex count.
a_sparse_three = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 1, 2]
    tgt = [2, 3, 3]
end

a_sparse_four = @acset Graphs.Graph begin
    V = 4
    E = 4
    src = [1, 1, 2, 3]
    tgt = [2, 3, 4, 4]
end

a_sparse_five = @acset Graphs.Graph begin
    V = 5
    E = 5
    src = [1, 1, 2, 3, 4]
    tgt = [3, 5, 5, 5, 5]
end

a_sparse_six = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [1, 2, 3, 5, 6, 6]
    tgt = [2, 3, 5, 4, 3, 5]
end

a_sparse_six2 = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [3, 2, 2, 1, 4, 5]
    tgt = [2, 1, 4, 5, 6, 6]
end

a_sparse_seven = @acset Graphs.Graph begin
    V = 7
    E = 7
    src = [1, 3, 4, 5, 6, 6, 7]
    tgt = [4, 1, 2, 3, 3, 4, 2]
end

a_sparse_eight = @acset Graphs.Graph begin
    V = 8
    E = 8
    src = [1, 2, 2, 3, 4, 6, 7, 8]
    tgt = [2, 3, 5, 7, 2, 4, 8, 5]
end

a_sparse_eight2 = @acset Graphs.Graph begin
    V = 8
    E = 8
    src = [1, 1, 2, 3, 3, 3, 4, 4]
    tgt = [3, 4, 4, 2, 7, 8, 5, 6]
end

# Acyclic Complete - Edge from each vertex to all vertices that do not form loops.
# Arranged in increasing vertex count.
# Naming scheme is based on vertex count.
a_complete_four = @acset Graphs.Graph begin
    V = 4
    E = 6
    src = [1, 1, 1, 2, 2, 3]
    tgt = [2, 3, 4, 3, 4, 4]
end

a_complete_six = @acset Graphs.Graph begin
    V = 6
    E = 15
    src = [1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5]
    tgt = [2, 3, 4, 5, 6, 3, 4, 5, 6, 4, 5, 6, 5, 6, 6]
end

# Directional checkerboard graphs - Acyclic
# Arranged in increasing vertex count.
# Naming scheme is based on graph vertex dimensions.
directional_box = @acset Graphs.Graph begin
    V = 4
    E = 4
    src = [1, 1, 2, 3]
    tgt = [2, 3, 4, 4]
end

directional_2x2 = @acset Graphs.Graph begin
    V = 9
    E = 12
    src = [1, 1, 2, 2, 3, 4, 4, 5, 5, 6, 7, 8]
    tgt = [2, 4, 3, 5, 6, 5, 7, 6, 8, 9, 8, 9]
end

# Linear (Path) Graphs
# Arranged in increasing vertex count.
# Naming scheme is based on vertex count.
line_two = @acset Graphs.Graph begin
    V = 2
    E = 1
    src = [1]
    tgt = [2]
end

line_three = @acset Graphs.Graph begin
    V = 3
    E = 2
    src = [1, 2]
    tgt = [2, 3]
end

line_four = @acset Graphs.Graph begin
    V = 4
    E = 3
    src = [1, 2, 3]
    tgt = [2, 3, 4]
end

line_five = @acset Graphs.Graph begin
    V = 5
    E = 4
    src = [1, 2, 3, 4]
    tgt = [2, 3, 4, 5]
end

line_six = @acset Graphs.Graph begin
    V = 6
    E = 5
    src = [1, 2, 3, 4, 5]
    tgt = [2, 3, 4, 5, 6]
end

line_seven = @acset Graphs.Graph begin
    V = 7
    E = 6
    src = [1, 2, 3, 4, 5, 6]
    tgt = [2, 3, 4, 5, 6, 7]
end

line_eight = @acset Graphs.Graph begin
    V = 8
    E = 7
    src = [1, 2, 3, 4, 5, 6, 7]
    tgt = [2, 3, 4, 5, 6, 7, 8]
end

#Undirected Path Graphs (can be used to generate undirected lattice/grid graphs)
# Arranged in increasing vertex count.
# Naming scheme is based on vertex count.
u_line_two = @acset Graphs.Graph begin
    V = 2
    E = 2
    src = [1, 2]
    tgt = [2, 1]
end

u_line_three = @acset Graphs.Graph begin
    V = 3
    E = 4
    src = [1, 2, 2, 3]
    tgt = [2, 3, 1, 2]
end

u_line_four = @acset Graphs.Graph begin
    V = 4
    E = 6
    src = [1, 2, 3, 2, 3, 4]
    tgt = [2, 3, 4, 1, 2, 3]
end

u_line_five = @acset Graphs.Graph begin
    V = 5
    E = 8
    src = [1, 2, 3, 4, 2, 3, 4, 5]
    tgt = [2, 3, 4, 5, 1, 2, 3, 4]
end

u_line_six = @acset Graphs.Graph begin
    V = 6
    E = 10
    src = [1, 2, 3, 4, 5, 2, 3, 4, 5, 6]
    tgt = [2, 3, 4, 5, 6, 1, 2, 3, 4, 5]
end

u_line_seven = @acset Graphs.Graph begin
    V = 7
    E = 12
    src = [1, 2, 3, 4, 5, 6, 2, 3, 4, 5, 6, 7]
    tgt = [2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6]
end

u_line_eight = @acset Graphs.Graph begin
    V = 8
    E = 14
    src = [1, 2, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 7, 8]
    tgt = [2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7]
end