# using Z3
using DReal
using Distributions
import Base.getindex
import Base:call


# If we're going row wise, the number of rows should change.
typealias NodeId Integer
typealias Weight Union(Real, DReal.Ex)
typealias NodeWeight Tuple{Integer, Weight}

"A Neural Network is a graph"
immutable NeuralNetwork
  # Edge going into first from second
  nlayers::Int
  layersizes::Vector{Int}
  in_edge::Dict{NodeId, Vector{NodeWeight}}
end

function nodesinlayer(nn::NeuralNetwork, l::Integer)
  lower = sum([nn.layersizes[i] for i=1:l-1]) + 1
  upper = lower + nn.layersizes[l] - 1
  collect(lower:upper)
end

"""Constructs a connected neural network where each node in layers 2 and above,
is randomly connected to `nchildren` from previous layer"""
function NeuralNetwork(nlayers::Int, layersizes::Vector{Int}, nchildren::Int)
  in_edge = Dict{NodeId, Vector{NodeWeight}}()
  nn = NeuralNetwork(nlayers, layersizes, Dict())
  for i = 2:nlayers
    nodeids = nodesinlayer(nn, i)
    prevlayer = nodesinlayer(nn, i-1)
    for nodeid in nodeids
      # Sample
      childrenids = sample(prevlayer, nchildren, replace=false)
      for childid in childrenids
        if haskey(nn.in_edge, nodeid)
          push!(nn.in_edge[nodeid], (childid, Var(Float64, -100., 100.)))
        else
          nn.in_edge[nodeid] = [(childid, Var(Float64, -100.0, 100.0))]
        end
      end
    end
  end
  nn
end

"Apply a Neural Network to a vector of inputs"
function call{T<:Real}(nn::NeuralNetwork, x::Vector{T})
  # Input size should math the row size
  @assert length(x) == nn.layersizes[1]
  # Initialise first row with input
  interm_values = Dict{Int, Any}([i => x[i] for i=1:nn.layersizes[1]])
  for i = 2:nn.nlayers
    nodeids = nodesinlayer(nn, i)
    for nodeid in nodeids
      weighted_children = nn.in_edge[nodeid]
      weighted_input = [interm_values[nodeid] * weight for (nodeid, weight) in weighted_children]
      summed = sum(weighted_input)
      output = rectifier(summed)
      interm_values[nodeid] = output
    end
  end

  outputnodes = nodesinlayer(nn, nn.nlayers)

  # Output last row
  [interm_values[i] for i in outputnodes]
end

"Rectifier Unit"
rectifier(x::Weight) = ifelse(x<0, 0.0, x)

function sqrdist(x::Array, y::Array)
  @assert length(x) == length(y)
  sum([(x[i] - y[i])^2 for i = 1:length(x)])
end

# Exmple
nn = NeuralNetwork(3, [3,4,2,1], 2)
nn([.3,.1,.3])
