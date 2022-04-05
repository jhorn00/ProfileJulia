# Simplicial Sets
using Catlab.Present
import Catlab.CategoricalAlgebra: elements
# Simplicial Sets
SUITE["ss"] = BenchmarkGroup()
SUITE["ss"]["testSS"] = @benchmarkable testSS()
# Define C-set
@present ThSemisimplicialSet(FreeSchema) begin
    (V, E, T)::Ob
    (d1, d2, d3)::Hom(T, E)
    (src, tgt)::Hom(E, V)
end
@acset_type SSet(ThSemisimplicialSet)

function repeat(n::Int)
    res = @acset SSet begin
        E = (n * (n - 1)) * 2 + (n - 1)^2
        V = n^2
    end
    coord = collect(Iterators.product(1:n, 1:n))
    v_d = Dict([(x, y) => i for (i, (x, y)) in enumerate(coord)])

    h_edge_d = Dict([(x, y) => i for (i, (x, y)) in enumerate(filter(c -> c[2] < n, coord))])

    v_edge_d = Dict([(x, y) => n * (n - 1) + i for (i, (x, y))
                     in
                     enumerate(filter(c -> c[1] < n, coord))])
    d_edge_d = Dict([(x, y) => 2 * n * (n - 1) + i for (i, (x, y))
                     in
                     enumerate(filter(c -> c[1] < n && c[2] < n, coord))])
    for (i, j) in coord
        if haskey(h_edge_d, (i, j))
            set_subparts!(res, h_edge_d[(i, j)]; (src=v_d[(i, j)], tgt=v_d[(i, j + 1)])...)
        end
        if haskey(v_edge_d, (i, j))
            set_subparts!(res, v_edge_d[(i, j)]; (src=v_d[(i + 1, j)], tgt=v_d[(i, j)])...)
        end
        if haskey(d_edge_d, (i, j))
            set_subparts!(res, d_edge_d[(i, j)]; (src=v_d[(i + 1, j + 1)], tgt=v_d[(i, j)])...)
        end
    end
    for (i, j) in filter(c -> c[1] < n && c[2] < n, coord)
        add_part!(res, :T, d1=h_edge_d[(i + 1, j)], d2=d_edge_d[(i, j)], d3=v_edge_d[(i, j)])
        add_part!(res, :T, d1=d_edge_d[(i, j)], d2=h_edge_d[(i, j)], d3=v_edge_d[(i, j + 1)])
    end

    return res

end

function repeat1d(n::Int)
    res = @acset SSet begin
        V = 2 * n
        #T = 2*(n-1)
        #E = 4*(n-1)+1
    end

    # Create horizontal edges
    edge_dict = Dict{Tuple{Int,Int},Int}()
    for i in 1:(n-1)
        edge_dict[(i, i + 1)] = add_part!(res, :E, src=i, tgt=i + 1)
        edge_dict[(i + n, i + n + 1)] = add_part!(res, :E, src=i + n, tgt=i + n + 1)
    end
    # Create vertical edges
    for i in 1:n
        edge_dict[(i, i + n)] = add_part!(res, :E, src=i, tgt=i + n)
    end
    # Create diagonal edges
    for i in 2:n
        edge_dict[(i, i + n - 1)] = add_part!(res, :E, src=i, tgt=i + n - 1)
    end

    # Add triangles
    for i in 1:n-1
        add_part!(res, :T, d1=edge_dict[(i, i + 1)], d2=edge_dict[(i + 1, i + n)], d3=edge_dict[(i, i + n)])
        add_part!(res, :T, d1=edge_dict[(i + 1, i + n)], d2=edge_dict[(i + n, i + n + 1)], d3=edge_dict[(i + 1, i + n + 1)])
    end

    return res
end

simplicialSets = Vector{SSet}()
for i in 1:10
    ss = repeat(i)
    push!(simplicialSets, ss)
end
simplicialSets
function testSS()
    homomorphism(simplicialSets[1], simplicialSets[2])
end
testSS()