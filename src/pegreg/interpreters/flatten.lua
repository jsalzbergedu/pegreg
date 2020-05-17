--------------------------------------------------------------------------------
-- Flatten trees of pairs into lists
--------------------------------------------------------------------------------
local flatten = {}

function flatten.state(n, final)
   return function (s, paired)
      return s.pair(s.state(n, final), paired)
   end
end

function flatten.arrow(from, to, input, output)
   return function (s, paired)
      return s.pair(s.arrow(from, to, input, output), paired)
   end
end

function flatten.pair(fst, snd)
   return function (s, paired)
      return fst(s, snd(s, paired))
   end
end

function flatten.null()
   return function (s, paired)
      return paired
   end
end

function flatten.create(states, arrows)
   return function (s)
      local states = states(s, s.null())
      local arrows = arrows(s, s.null())
      return s.create(states, arrows)
   end
end

return flatten
