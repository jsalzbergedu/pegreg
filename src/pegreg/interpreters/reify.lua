local data_structures = require("pegreg.data_structures")

local list = data_structures.list
local nfst = data_structures.nfst

--- An interpreter that takes
--- the input DSL
--- list and transforms it into the
--- "nfst" data structure.
---
--- Its working type is a list, and
--- its create type is an nfst.
local reify = {}

function reify.pair(fst, snd)
   local out = list.new()
   for _, v in ipairs(fst) do
      out:add(v)
   end
   for _, v in ipairs(snd) do
      out:add(v)
   end
   return out
end

function reify.state(n, final)
   return list.new(nfst.state.new(n, final))
end

function reify.arrow(from, to, input, output)
   return list.new(nfst.arrow.new(from, to, input, output))
end

function reify.null()
   return list.new()
end

function reify.create(states, arrows)
   return nfst.nfst.new(states, arrows)
end

return reify
