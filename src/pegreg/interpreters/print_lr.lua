local l = require("pegreg.frontends.language")
local print_syntax = require("pegreg.interpreters.print_syntax")

local print_lr = {}

for k, v in pairs(print_syntax) do
   print_lr[k] = v
end

function print_lr.left(item)
   return string.format("(left %s)", item)
end

function print_lr.right(item)
   return string.format("(right %s)", item)
end

return print_lr
