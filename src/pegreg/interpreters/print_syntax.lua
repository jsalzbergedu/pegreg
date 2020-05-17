--------------------------------------------------------------------------------
-- Interpreter that pretty-prints the syntax.
--------------------------------------------------------------------------------
local print_syntax = {}

function print_syntax.e()
   local out = "(empty)"
   return out
end

function print_syntax.lit(lit)
   local out = string.format("(lit %s)", lit)
   return out
end

function print_syntax.seq(rule1, rule2)
   local out = string.format("(seq %s %s)", rule1, rule2)
   return out
end

function print_syntax.choice(rule1, rule2)
   local out = string.format("(choice %s %s)", rule1, rule2)
   return out
end

function print_syntax.grammar(item)
   local out = string.format("(grammar %s)", item)
   return out
end

function print_syntax.ref(rule, rules)
   local out = string.format("(ref %s)", rule)
   return out
end

function print_syntax.star(item)
   local out = string.format("(star %s)", rule)
   return out
end

function print_syntax.create(grammar)
   local out = string.format("(create %s)", grammar)
   print(out)
   return out
end

return print_syntax
