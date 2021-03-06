--------------------------------------------------------------------------------
-- A print interpreter for the states
--------------------------------------------------------------------------------
local print_nfa = {}

function print_nfa.state(n, final)
   return string.format("(state %d %s)", n, final)
end

function print_nfa.arrow(from, to, input)
   if input == '' then
      input = 'ε'
   end
   return string.format("(arrow %d %d %s)", from, to, input)
end

function print_nfa.pair(fst, snd)
   if snd == "" then
      return fst
   end
   return string.format("%s %s", fst, snd)
end

function print_nfa.null()
   return ""
end

function print_nfa.create(states, arrows)
   local out = string.format("(create (states (%s)) (arrows (%s)))", states, arrows)
   print(out)
   return out
end

return print_nfa
