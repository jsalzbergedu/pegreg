local reify = {}

reify.pair_mt = {}

function reify.pair_mt.__tostring(pair)
   local out = "("
   if #pair > 0 then
      out = out .. tostring(pair[1])
   end
   for i = 2, #pair, 1 do
      out = out .. " " .. tostring(pair[i])
   end
   out = out .. ")"
   return out
end


function reify.pair(fst, snd)
   local out = {}
   for _, v in ipairs(fst) do
      table.insert(out, v)
   end
   for _, v in ipairs(snd) do
      table.insert(out, v)
   end
   setmetatable(out, reify.pair_mt)
   return out
end

reify.state_mt = {}

function reify.state_mt.__tostring(state)
   return string.format("(state %d %s)", state.number, state.final)
end

function reify.state_mt.__eq(state1, state2)
   return state1.number == state2.number
end

function reify.state_mt.__lt(state1, state2)
   return state1.number < state2.number
end

function reify.state_mt.__le(state1, state2)
   return state1.number <= state2.number
end

function reify.state(n, final)
   local out_el = {
      number = n,
      final = final
   }
   setmetatable(out_el, reify.state_mt)
   local out = {out_el}
   setmetatable(out, reify.pair_mt)
   return out
end

reify.arrow_mt = {}

function reify.arrow_mt.__tostring(arrow)
   local input = arrow.input
   local output = arrow.output
   if input == '' then
      input = "ε"
   end
   if output == '' then
      output = "ε"
   end
   return string.format("(arrow %d %d %s %s)",
                        arrow.from,
                        arrow.to,
                        input,
                        output)
end

function reify.arrow_mt.__eq(arrow1, arrow2)
   if arrow1.from ~= arrow2.from then
      return false
   end
   if arrow1.to ~= arrow2.to then
      return false
   end
   return true
end

function reify.arrow_mt.__lt(arrow1, arrow2)
   if arrow1.from == arrow2.from then
      return arrow1.to < arrow2.to
   end
   return arrow1.from < arrow2.from
end

function reify.arrow_mt.__le(arrow1, arrow2)
   if arrow1.from == arrow2.from then
      return arrow1.to <= arrow2.to
   end
   return arrow1.from <= arrow2.from
end

function reify.arrow(from, to, input, output)
   local out_el = {
      from = from,
      to = to,
      input = input,
      output = output
   }
   setmetatable(out_el, reify.arrow_mt)
   local out = {out_el}
   setmetatable(out, reify.pair_mt)
   return out
end

function reify.null()
   local out = {}
   setmetatable(out, reify.pair_mt)
   return out
end

reify.reified_mt = {}

function reify.reified_mt.__tostring(reified)
   return string.format("(reified (states %s) (arrows %s))",
                        reified.states,
                        reified.arrows)
end

function reify.create(states, arrows)
   local out = {
      states = states,
      arrows = arrows
   }
   setmetatable(out, reify.reified_mt)
   return out
end

return reify
