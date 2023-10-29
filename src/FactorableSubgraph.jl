abstract type AbstractFactorableSubgraph end
abstract type DominatorSubgraph <: AbstractFactorableSubgraph end
abstract type PostDominatorSubgraph <: AbstractFactorableSubgraph end

"""
    FactorableSubgraph{T<:Integer,S<:AbstractFactorableSubgraph}

# Fields

- `graph::DerivativeGraph{T}`
- `subgraph::Tuple{T,T}`
- `times_used::T`
- ` reachable_non_dominance::BitVector`
- `dominance_mask::BitVector`
"""
struct FactorableSubgraph{T<:Integer,S<:AbstractFactorableSubgraph}
    graph::DerivativeGraph{T}
    subgraph::Tuple{T,T}
    times_used::T
    reachable_non_dominance::BitVector
    dominance_mask::BitVector

    function FactorableSubgraph{T,DominatorSubgraph}(graph::DerivativeGraph{T}, dominating_node::T, dominated_node::T, dom_mask::BitVector, non_dom_mask::BitVector) where {T<:Integer}
        @assert dominating_node > dominated_node

        return new{T,DominatorSubgraph}(graph, (dominating_node, dominated_node), sum(dom_mask) * sum(non_dom_mask), non_dom_mask, dom_mask)
    end

    function FactorableSubgraph{T,PostDominatorSubgraph}(graph::DerivativeGraph{T}, dominating_node::T, dominated_node::T, pdom_mask::BitVector, non_dom_mask::BitVector) where {T<:Integer}
        @assert dominating_node < dominated_node

        return new{T,PostDominatorSubgraph}(graph, (dominating_node, dominated_node), sum(non_dom_mask) * sum(pdom_mask), non_dom_mask, pdom_mask)
    end
end

FactorableSubgraph(args::Tuple) = FactorableSubgraph(args...)



function dominator_subgraph(graph::DerivativeGraph{T}, dominating_node::T, dominated_node::T, dom_mask::BitVector) where {T}
    #find reachable_variables
    pedges = parent_edges(graph, dominated_node)
    rvars = falses(domain_dimension(graph))

    for edge in pedges
        if any(dom_mask .& reachable_roots(edge)) #edge belongs to the subgraph
            rvars .= rvars .| reachable_variables(edge)
        end
    end

    return FactorableSubgraph{T,DominatorSubgraph}(graph, dominating_node, dominated_node, dom_mask, rvars)
end


function postdominator_subgraph(graph::DerivativeGraph{T}, dominating_node::T, dominated_node::T, pdom_mask::BitVector) where {T}
    #find reachable_variables
    cedges = child_edges(graph, dominated_node)
    rroots = falses(codomain_dimension(graph))

    for edge in cedges
        if any(pdom_mask .& reachable_variables(edge)) #edge belongs to the subgraph
            rroots .= rroots .| reachable_roots(edge)
        end
    end

    return FactorableSubgraph{T,PostDominatorSubgraph}(graph, dominating_node, dominated_node, pdom_mask, rroots)
end

graph(a::FactorableSubgraph) = a.graph

"""
    vertices(subgraph::FactorableSubgraph)

Returns a tuple of ints (dominator vertex,dominated vertex) that are the top and bottom vertices of the subgraph"""
vertices(subgraph::FactorableSubgraph) = subgraph.subgraph


reachable_variables(a::FactorableSubgraph{T,DominatorSubgraph}) where {T} = a.reachable_non_dominance
reachable_roots(a::FactorableSubgraph{T,DominatorSubgraph}) where {T} = a.dominance_mask

reachable_variables(a::FactorableSubgraph{T,PostDominatorSubgraph}) where {T} = a.dominance_mask
reachable_roots(a::FactorableSubgraph{T,PostDominatorSubgraph}) where {T} = a.reachable_non_dominance

reachable_non_dominance(a::FactorableSubgraph{T,DominatorSubgraph}) where {T} = a.reachable_non_dominance
reachable_non_dominance(a::FactorableSubgraph{T,PostDominatorSubgraph}) where {T} = a.reachable_non_dominance

reachable_dominance(a::FactorableSubgraph) = a.dominance_mask

function mask_variables!(a::FactorableSubgraph, mask::BitVector)
    @assert domain_dimension(graph(a)) == length(mask)
    a.reachable_variables .&= mask
end


function mask_roots!(a::FactorableSubgraph, mask::BitVector)
    @assert codomain_dimension(graph(a)) == length(mask)
    a.reachable_roots .&= mask
end




dominating_node(a::FactorableSubgraph{T,S}) where {T,S<:Union{DominatorSubgraph,PostDominatorSubgraph}} = a.subgraph[1]

dominated_node(a::FactorableSubgraph{T,S}) where {T,S<:Union{DominatorSubgraph,PostDominatorSubgraph}} = a.subgraph[2]


times_used(a::FactorableSubgraph) = a.times_used


node_difference(a::FactorableSubgraph) = abs(a.subgraph[1] - a.subgraph[2])

function Base.show(io::IO, a::FactorableSubgraph)
    print(io, summarize(a))
end

function summarize(a::FactorableSubgraph{T,DominatorSubgraph}) where {T}
    doms = ""
    doms *= to_string(reachable_dominance(a), "r")
    doms *= " ↔ "
    doms *= to_string(reachable_variables(a), "v")

    return "[" * doms * " $(times_used(a))* " * string((vertices(a))) * "]"
end


function summarize(a::FactorableSubgraph{T,PostDominatorSubgraph}) where {T}
    doms = ""
    doms *= to_string(reachable_roots(a), "r")
    doms *= " ↔ "
    doms *= to_string(reachable_dominance(a), "v")

    return "[" * doms * " $(times_used(a))* " * string((vertices(a))) * "]"
end


"""
    forward_edges(a::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge)

Returns parent edges if subgraph is dominator and child edges otherwise. Parent edges correspond to the forward traversal of a dominator subgraph in graph factorization, analogously for postdominator subgraph"""
forward_edges(a::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = parent_edges(graph(a), edge)
forward_edges(a::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = child_edges(graph(a), edge)

forward_edges(a::FactorableSubgraph{T,DominatorSubgraph}, node_index::T) where {T} = parent_edges(graph(a), node_index)
forward_edges(a::FactorableSubgraph{T,PostDominatorSubgraph}, node_index::T) where {T} = child_edges(graph(a), node_index)


"""
    backward_edges(a::FactorableSubgraph{T,DominatorSubgraph}, node_index::T)

Returns child edges if subgraph is dominator and parent edges otherwise. Child edges correspond to the backward check for paths bypassing the dominated node of a dominator subgraph, analogously for postdominator subgraph"""
backward_edges(a::FactorableSubgraph{T,DominatorSubgraph}, node_index::T) where {T} = child_edges(graph(a), node_index)
backward_edges(a::FactorableSubgraph{T,PostDominatorSubgraph}, node_index::T) where {T} = parent_edges(graph(a), node_index)

backward_edges(a::FactorableSubgraph, edge::PathEdge) = backward_edges(a, backward_vertex(a, edge))

"""returns true if `edge` is on a valid path from the `dominated_node(a)` to the `dominating_node(a)`, i.e., the edge is in the subgraph.

# Note: this is legal: `reachable_variables(a) ⊄ reachable_variables(edge)`. This is counterintuitive because it appears to imply that there are paths through the subgraph that are not allowed by the edge. This is not the case. The missing paths have been accounted for in a previous factorization."""
# test_edge(a::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = subset(reachable_dominance(a), reachable_roots(edge)) && overlap(reachable_variables(a), reachable_variables(edge))
# """returns true if `edge` is on a valid path from the `dominated_node(a)` to the `dominating_node(a)`, i.e., the edge is in the subgraph.

# Note: this is legal: `reachable_roots(a) ⊄ reachable_roots(edge)`. This is counterintuitive because it appears to imply that there are paths through the subgraph that are not allowed by the edge. This is not the case. The missing paths have been accounted for in a previous factorization."""
# test_edge(a::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = subset(reachable_dominance(a), reachable_variables(edge)) && overlap(reachable_roots(a), reachable_roots(edge))

"""Note: this is legal: `reachable_variables(a) ⊄ reachable_variables(edge)`. This is counterintuitive because it appears to imply that there are paths through the subgraph that are not allowed by the edge. This is not the case. The missing paths have been accounted for in a previous factorization."""
test_edge(a::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = overlap(reachable_dominance(a), reachable_roots(edge)) && overlap(reachable_non_dominance(a), reachable_variables(edge))
"""returns true if `edge` is on a valid path from the `dominated_node(a)` to the `dominating_node(a)`, i.e., the edge is in the subgraph.

Note: this is legal: `reachable_roots(a) ⊄ reachable_roots(edge)`. This is counterintuitive because it appears to imply that there are paths through the subgraph that are not allowed by the edge. This is not the case. The missing paths have been accounted for in a previous factorization."""
test_edge(a::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = overlap(reachable_dominance(a), reachable_variables(edge)) && overlap(reachable_non_dominance(a), reachable_roots(edge))


reachable_dominance(::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = reachable_roots(edge)
reachable_dominance(::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = reachable_variables(edge)
reachable_non_dominance(::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = reachable_variables(edge)
reachable_non_dominance(::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = reachable_roots(edge)

non_dominance_mask(::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = reachable_variables(edge)
non_dominance_mask(::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = reachable_roots(edge)



non_dominance_dimension(subgraph::FactorableSubgraph{T,DominatorSubgraph}) where {T} = domain_dimension(graph(subgraph))
non_dominance_dimension(subgraph::FactorableSubgraph{T,PostDominatorSubgraph}) where {T} = codomain_dimension(graph(subgraph))

dominance_dimension(subgraph::FactorableSubgraph{T,DominatorSubgraph}) where {T} = codomain_dimension(graph(subgraph))
dominance_dimension(subgraph::FactorableSubgraph{T,PostDominatorSubgraph}) where {T} = domain_dimension(graph(subgraph))

forward_vertex(::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = top_vertex(edge)
forward_vertex(::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = bott_vertex(edge)

backward_vertex(::FactorableSubgraph{T,DominatorSubgraph}, edge::PathEdge) where {T} = bott_vertex(edge)
backward_vertex(::FactorableSubgraph{T,PostDominatorSubgraph}, edge::PathEdge) where {T} = top_vertex(edge)

function next_valid_edge(a::FactorableSubgraph, current_edge::PathEdge{T}) where {T}
    if forward_vertex(a, current_edge) == dominating_node(a) #reached the end of the subgraph
        return nothing
    else
        local edge_next::PathEdge{T}
        count = 0
        for edge in forward_edges(a, current_edge) #should always be a next edge because top_vertex(current_edge) != dominance_node(a)
            if test_edge(a, edge)
                count += 1

                if count > 1
                    return nothing
                end
                edge_next = edge
            end
        end
        if count == 0
            return nothing #no valid next edge. This can occur if reachable variables or roots were reset by a previous factorization step.
        else
            return edge_next
        end
    end
end

function isa_connected_path(a::FactorableSubgraph, start_edge::PathEdge{T}) where {T}
    current_edge = start_edge

    if test_edge(a, start_edge) #ensure that start_edge satisfies conditions for being on a connected path
        while forward_vertex(a, current_edge) != dominating_node(a)
            current_edge = next_valid_edge(a, current_edge)
            if current_edge === nothing
                return false
            end
        end
        return true
    else
        return false
    end
end


"""
split_non_dom_edges!(subgraph::FactorableSubgraph{T,S})

Splits edges which have roots not in the `dominance_mask` of `subgraph`. Resets the reachability mask of dominated edges and and returns a list of new edges that have reachability mask corresponding to the non-dominant roots or variables."""
function find_non_dom_edges(subgraph::FactorableSubgraph{T,S}, sub_edges) where {T,S<:AbstractFactorableSubgraph}
    temp_edges = PathEdge{T}[]

    for sub_edge in sub_edges
        edge_mask = reachable_dominance(subgraph, sub_edge)
        some_dom_reachable = any(reachable_dominance(subgraph) .& edge_mask) #see if some reachable roots or variables are in the dominance set of the edge.
        if (some_dom_reachable)
            diff = set_diff(edge_mask, reachable_dominance(subgraph)) #important that diff is a new BitVector, not reused.
            if any(diff) #see if some roots or variables not in dominance set are in the reachable set of the edge. Split if true.
                if S === DominatorSubgraph
                    push!(temp_edges, PathEdge(top_vertex(sub_edge), bott_vertex(sub_edge), value(sub_edge), copy(reachable_variables(sub_edge)), diff)) #create a new edge that accounts for roots not in the dominance mask
                else

                    push!(temp_edges, PathEdge(top_vertex(sub_edge), bott_vertex(sub_edge), value(sub_edge), diff, copy(reachable_roots(sub_edge)))) #create a new edge that accounts for roots not in the     dominance mask    
                end
            end
        end
    end

    #non-dom edges should not have zero reachability
    for edge in temp_edges
        @assert any(reachable_dominance(subgraph, edge)) "This is a bug. Please create an issue on the FastDifferentiation.jl repo."
        @assert any(reachable_non_dominance(subgraph, edge)) "This is a bug. Please create an issue on the FastDifferentiation.jl repo."
    end

    return temp_edges
end


function check_edges(subgraph::FactorableSubgraph{T,S}, edge_list::Vector{PathEdge{T}}) where {T,S}
    #make sure have at least two edges that are on a valid path from dominated to dominating node
    count = 0
    for edge in edge_list
        if test_edge(subgraph, edge)
            count += 1
        end
    end
    return count
end


"""verifies that every edge in `subgraph_edges(subgraph)` is on a path from `dominating_node(subgraph)` to `dominated_node(subgraph)`. This is done by testing for the following properties:

for e ∈ subgraph_edges(subgraph)
    either forward_vertex(e) has children or it is equal to `dominated_node`
    either backward_vertex(e) has parents or it is equal to `dominating_node`
end
"""
function verify_subgraph_paths(subgraph::FactorableSubgraph{T}, subedges) where {T}
    backward_vertices = Dict{T,Set{T}}()

    for edge in subedges
        back = backward_vertex(subgraph, edge)
        fwd = forward_vertex(subgraph, edge)
        chld_verts = get(backward_vertices, fwd, nothing)
        if chld_verts === nothing
            backward_vertices[fwd] = Set{T}()
        end
        push!(backward_vertices[fwd], back)

    end

    @assert get(backward_vertices, dominated_node(subgraph), nothing) === nothing "This is a bug. Please create an issue on the FastDifferentiation.jl repo."

    backward_vertices[dominated_node(subgraph)] = Set{T}() #dominated node has no forward vertices

    for prnt in keys(backward_vertices)
        back_verts = backward_vertices[prnt]
        for backward in back_verts
            back_back_verts = get(backward_vertices, backward, nothing)
            @assert back_back_verts !== nothing "a child vertex wasn't found. This is a bug. Please create an issue on the FastDifferentiation.jl repo. \n\n Debug info: subgraph vertices $(vertices(subgraph)) subedges $(vertices.(subedges)) backward_vertices $backward_vertices. "

            if length(back_back_verts) == 0
                @assert backward == dominated_node(subgraph)
            end
        end
    end

    forward_vertices = Dict{T,Set{T}}()

    for edge in subedges
        back = backward_vertex(subgraph, edge)
        fwd = forward_vertex(subgraph, edge)
        chld_verts = get(forward_vertices, back, nothing)
        if chld_verts === nothing
            forward_vertices[back] = Set{T}()
        end
        push!(forward_vertices[back], fwd)

    end

    @assert get(forward_vertices, dominating_node(subgraph), nothing) === nothing "This is a bug. Please create an issue on the FastDifferentiation.jl repo."

    forward_vertices[dominating_node(subgraph)] = Set{T}() #dominated node has no forward vertices

    for prnt in keys(forward_vertices)
        fwd_verts = forward_vertices[prnt]
        for backward in fwd_verts
            fwd_fwd_verts = get(forward_vertices, backward, nothing)
            @assert fwd_fwd_verts !== nothing "a child vertex wasn't found. This is a bug. Please create an issue on the FastDifferentiation.jl repo. \n\n Debug info: subgraph vertices $(vertices(subgraph)) subedges $(vertices.(subedges)) forward_vertices $forward_vertices."

            if length(fwd_fwd_verts) == 0
                @assert backward == dominating_node(subgraph)
            end
        end
    end

end

"""Finds edges in the subgraph, if the subgraph still exists. If the subgraph doesn't exist then returns the empty set."""
function subgraph_edges(subgraph::FactorableSubgraph{T}) where {T}
    sub_edges = Set{PathEdge{T}}()
    valid_subgraph = subgraph_edges!(sub_edges, subgraph, dominated_node(subgraph))

    if length(sub_edges) == 0 || !valid_subgraph
        empty!(sub_edges)
        return sub_edges
    end

    #have guaranteed that for each valid subgraph edge there is a path from the dominated node to the dominating node. Now need to verify that these edges constitute a factorable subgraph.
    count = 0
    for edge in backward_edges(subgraph, dominating_node(subgraph))
        if edge ∈ sub_edges
            count += 1
        end
    end

    if count < 2
        empty!(sub_edges)
        return sub_edges
    end

    count = 0
    for edge in forward_edges(subgraph, dominated_node(subgraph))
        if edge ∈ sub_edges
            count += 1
        end
    end

    if count < 2
        empty!(sub_edges)
        return sub_edges
    end

    if length(sub_edges) > 0
        verify_subgraph_paths(subgraph, sub_edges)
    end

    return sub_edges
end

"""
    subgraph_edges!(
        sub_edges::Union{Nothing,Set{PathEdge{T}}}=nothing,
        subgraph::FactorableSubgraph{T},       
        visited::Union{Nothing,Set{PathEdge{T}}}=nothing,
        curr_node::Union{Nothing,T}=nothing
    )

Returns all edges in the subgraph as a set. Recursively traverses the subgraph so will work even for subgraphs with branching paths."""
function subgraph_edges!(sub_edges::Set{PathEdge{T}}, subgraph::FactorableSubgraph{T}, curr_node::T) where {T}
    if curr_node == dominating_node(subgraph)
        return true
    else
        fedges = forward_edges(subgraph, curr_node)
        path_forward = false

        #this handles the case when there are either no forward edges or none of the forward edges are valid subgraph edges.
        for fedge in fedges
            if test_edge(subgraph, fedge)
                path_forward = true
            end
        end

        if !path_forward
            return false
        end

        #recurse to verify other edges all satisfy invariant
        for fedge in forward_edges(subgraph, curr_node)
            if test_edge(subgraph, fedge) #there is a valid path forward
                push!(sub_edges, fedge)
                fvert = forward_vertex(subgraph, fedge)
                tmp = subgraph_edges!(sub_edges, subgraph, fvert)
                if !tmp
                    return tmp #at least one broken path from dominated node to dominating node
                end
            end
        end
        return true #tested all the valid forward paths and none asserted false so all forward paths from this vertex make it to the dominating node.
    end
end



"""
    deconstruct_subgraph(subgraph::FactorableSubgraph)

Returns subgraph edges, as a `Set`, and nodes, as a `Vector`."""
function deconstruct_subgraph(subgraph::FactorableSubgraph{T}) where {T}
    sub_edges = subgraph_edges(subgraph)
    if length(sub_edges) > 0

        sub_nodes = map(x -> backward_vertex(subgraph, x), collect(sub_edges))
        push!(sub_nodes, dominating_node(subgraph)) #dominating node will not be the backward vertex of any edge
        return sub_edges, unique(sub_nodes)
    else
        return nothing
    end
end

# """
#     subgraph_exists(subgraph::FactorableSubgraph)

# Returns true if the subgraph is still a factorable subgraph, false otherwise"""
# function subgraph_exists(subgraph::FactorableSubgraph, sub_edges)
#     dominated_edges, dominating_edges = dom_nodes_edge_count(subgraph, sub_edges)
#     if length(dominated_edges) == 0 || length(dominating_edges) == 0 #either or both of dominating/dominated node are not present in nodes of sub_edges so subgraph has been destroyed by previous factorization.
#         return false
#     else
#         tmp = is_branching(subgraph, sub_edges)

#         if tmp#subgraph_edges recursively visits the subgraph edges from the dominated to the dominating node. check_sub_edges returned true, which means the dominated and dominating vertices are present in the vertices of sub_edges. This means there must be at least one path from the dominated to the dominating vertex
#             return true
#         else
#             #subgraph isn't branching so isa_connected_path should work correctly

#             #Do fast tests that guarantee subgraph has been destroyed by factorization: no edges connected to dominated node, dominated_node or dominator node has < 2 subgraph edges
#             #This is inefficient since many tests require just the number of edges but this code creates temp arrays containing the edges and then measures the length. Optimize later by having separate children and parents fields in edges structure of RnToRmGraph. Then num_parents and num_children become fast and allocation free.

#             #in a non-branching graph need at least two subgraph edges incident on the dominated_node and the dominating_node. Otherwise subgraph has been destroyed by a previous factorization.
#             if length(dominated_edges) < 2 || length(dominating_edges) < 2
#                 return false
#             else
#                 count = 0
#                 sub_edges = Set{PathEdge}()

#                 for edge in dominated_edges
#                     if isa_connected_path(subgraph, edge) !== nothing
#                         count += 1
#                     end
#                 end
#                 if count >= 2 #only have a valid subgraph if there are at least two complete paths from the dominated to the dominating node
#                     return true
#                 else
#                     return false
#                 end
#             end
#         end
#     end
# end

#PathIterator has redundant computation because path is checked for connectivity when creating iterator and then path is traversed again when running iterator. Not sure how if it is possible to use Iterator framework without doing this, or making the calling code much more complex.
struct PathIterator{T<:Integer,S<:FactorableSubgraph}
    subgraph::S
    start_edge::PathEdge{T}

    function PathIterator(subgraph::S, start_edge::PathEdge{T}) where {T,S<:FactorableSubgraph{T,DominatorSubgraph}}
        @assert bott_vertex(start_edge) == dominated_node(subgraph) "This is a bug. Please create an issue on the FastDifferentiation.jl repo."
        return new{T,S}(subgraph, start_edge)
    end

    function PathIterator(subgraph::S, start_edge::PathEdge{T}) where {T,S<:FactorableSubgraph{T,PostDominatorSubgraph}}
        @assert top_vertex(start_edge) == dominated_node(subgraph) "This is a bug. Please create an issue on the FastDifferentiation.jl repo."
        return new{T,S}(subgraph, start_edge)
    end
end


edge_path(subgraph::FactorableSubgraph, start_edge) = PathIterator(subgraph, start_edge)


"""
    Base.iterate(a::PathIterator{T,S})

Returns an iterator for a single path in a factorable subgraph. If the path has been destroyed by factorization returns nothing."""
function Base.iterate(a::PathIterator{T,S}) where {T,S<:FactorableSubgraph}
    if !isa_connected_path(a.subgraph, a.start_edge)
        return nothing
    else
        return (a.start_edge, a.start_edge)
    end
end

function Base.iterate(a::PathIterator{T,S}, state::PathEdge{T}) where {T,S<:FactorableSubgraph}
    if forward_vertex(a.subgraph, state) == dominating_node(a.subgraph)
        return nothing
    else
        edge_next = next_valid_edge(a.subgraph, state)

        @assert edge_next !== nothing #tested for connected path when creating iterator so should never get nothing return because edge is not at the dominator node

        return (edge_next, edge_next)
    end
end

Base.IteratorSize(::Type{<:PathIterator}) = Base.SizeUnknown()
Base.IteratorEltype(::Type{<:PathIterator}) = Base.HasEltype()
Base.eltype(::Type{<:PathIterator{T}}) where {T} = PathEdge{T}


function r1r1subgraph_edges(graph::DerivativeGraph{T}, root_index::T, variable_index::T) where {T}
    visited = Set{T}()
    sub_edges = Set{PathEdge}()
    return _r1r1subgraph_edges(graph, root_index_to_postorder_number(graph, root_index), root_index, variable_index, visited, sub_edges)
end


"""
    _r1r1subgraph_edges(
        graph::DerivativeGraph{T},
        current_index::T,
        root_index::T,
        variable_index::T,
        visited::Set{T},
        sub_edges::Set{PathEdge}
    )

Returns the edges in the subgraph connecting `root_index` and `variable_index`. This is an R¹->R¹ function. Used for debugging."""
function _r1r1subgraph_edges(graph::DerivativeGraph{T},
    current_index::T,
    root_index::T,
    variable_index::T,
    visited::Set{T},
    sub_edges::Set{PathEdge}) where {T}

    if !in(current_index, visited)
        push!(visited, current_index)
        for child in child_edges(graph, current_index)
            if reachable_roots(child)[root_index]#&& reachable_variables(child)[variable_index]
                push!(sub_edges, child)
                _r1r1subgraph_edges(graph, bott_vertex(child), root_index, variable_index, visited, sub_edges)
            end
        end
    end

    return sub_edges
end

"""
    graph_array(subgraph::DominatorSubgraph)

Finds the node indices in the subgraph. Computes relations for each node (indices of parents inside subgraph for dom, children for pdom. Returns two vectors: the indices of the graph nodes, and a vector of vectors that contains the relations informations."""
function graph_array(subgraph::DominatorSubgraph)

end
