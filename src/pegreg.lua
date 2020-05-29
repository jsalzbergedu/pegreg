local library = {}

local interpreters = require("pegreg.interpreters")
local frontends = require("pegreg.frontends")
local compiler = require("pegreg.compiler")

for k, v in pairs(interpreters) do
   library[k] = v
end

for k, v in pairs(frontends) do
   library[k] = v
end

for k, v in pairs(compiler) do
   library[k] = v
end

return library
