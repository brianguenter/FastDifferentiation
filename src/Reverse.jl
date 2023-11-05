function reverse_AD(a::DerivativeGraph, root_index::T, variable_order::AbstractVector{<:Node}) where {T<:Integer}


    let visited = Dict{Int64,Tuple{Int64,Node}}()
        all_vars = zeros(Node, domain_dimension(a))

        function _reverseAD(a::DerivativeGraph, curr_deriv::Node, curr_vertex::Int64, all_vars, visited)
            if (tmp = get(visited, curr_vertex, nothing)) === nothing
                visited[curr_vertex] = (1, curr_deriv)
            else
                visit_count, val = visited[curr_vertex]
                visited[curr_vertex] = (visit_count + 1, val + curr_deriv)
            end

            visit_count, val = visited[curr_vertex]

            prnt_edges = count(x -> reachable_roots(x)[root_index], parent_edges(a, curr_vertex))
            if visit_count < prnt_edges && curr_vertex != root_index_to_postorder_number(a, root_index) #want to recurse immediately if started at a root with parents
                return
            else
                for c_edge in child_edges(a, curr_vertex)
                    _reverseAD(a, val * value(c_edge), bott_vertex(c_edge), all_vars, visited)
                end

                if is_variable(a, curr_vertex)
                    all_vars[variable_postorder_to_index(a, curr_vertex)] = val
                end
            end
        end


        _reverseAD(a, one(Node), root_index_to_postorder_number(a, root_index), all_vars, visited)

        result = Vector{Node}(undef, length(variable_order))

        #now map variable values to variable_order
        for (i, _) in pairs(variable_order)
            result[i] = all_vars[i]
        end

        return result
    end
end
export reverse_AD

function reverse_AD(a::Node, variable_order::AbstractVector{<:Node})
    if length(variables(a)) == 0
        return zeros(Node, length(variable_order))
    else
        return reverse_AD(DerivativeGraph(a), variable_order)
    end
end

function reverse_AD(a::DerivativeGraph)
    rev_jac = Matrix{Node}(undef, codomain_dimension(a), domain_dimension(a))
    for (i, _) in pairs(roots(a))
        rev_jac[i, :] .= reverse_AD(a, i, variables(a))
    end
    return rev_jac
end