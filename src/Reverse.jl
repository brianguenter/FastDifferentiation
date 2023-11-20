"""This function can be very slow because it has to traverse a graph where some paths may not be followed due to factorization. Has to traverse every `m*n` path where `m` is number of roots and `n` is number of variables."""
function reverse_AD(a::DerivativeGraph, root_index::T, variable_number::T) where {T<:Integer}
    let visited = Dict{Int64,Tuple{Int64,Node}}()
        one_result = zero(Node)

        function _reverseAD(a::DerivativeGraph, curr_deriv::Node, curr_vertex::Int64, visited)
            if (tmp = get(visited, curr_vertex, nothing)) === nothing
                visited[curr_vertex] = (1, curr_deriv)
            else
                visit_count, val = visited[curr_vertex]
                visited[curr_vertex] = (visit_count + 1, val + curr_deriv)
            end

            visit_count, val = visited[curr_vertex]

            prnt_edges = count(x -> reachable_roots(x)[root_index] && reachable_variables(x)[variable_number], parent_edges(a, curr_vertex)) #only count those edges which are reachable from the root and variable under consideration.

            if curr_vertex == root_index_to_postorder_number(a, root_index) || visit_count == prnt_edges   #want to recurse immediately if started at a root with parents
                for c_edge in child_edges(a, curr_vertex)
                    if reachable_roots(c_edge)[root_index] && reachable_variables(c_edge)[variable_number]
                        _reverseAD(a, val * value(c_edge), bott_vertex(c_edge), visited)
                    end
                end

                if is_variable(a, curr_vertex)
                    @assert variable_index_to_postorder_number(a, variable_number) == curr_vertex #should only be able to descend to a single variable
                    one_result = val
                end
            else
                return
            end
        end

        root_postorder = root_index_to_postorder_number(a, root_index)

        _reverseAD(a, one(Node), root_postorder, visited)

        return one_result
    end
end
export reverse_AD



function reverse_AD(a::DerivativeGraph, vars::Vector{Node}=variables(a))
    rev_jac = Matrix{Node}(undef, codomain_dimension(a), domain_dimension(a))
    var_indices = variable_node_to_index.(Ref(a), vars)

    for (i, _) in pairs(roots(a))
        for (j, col) in pairs(var_indices)
            rev_jac[i, j] = reverse_AD(a, i, col)
        end
    end
    return rev_jac
end