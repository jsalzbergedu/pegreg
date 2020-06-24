local library = {}

local interpreters = require("pegreg.interpreters")
local frontends = require("pegreg.frontends")
local compiler = require("pegreg.compiler")
local data_structures = require("pegreg.data_structures")
local algorithms = require("pegreg.algorithms")

for k, v in pairs(interpreters) do
   library[k] = v
end

for k, v in pairs(frontends) do
   library[k] = v
end

for k, v in pairs(compiler) do
   library[k] = v
end

for k, v in pairs(data_structures) do
   library[k] = v
end

for k, v in pairs(algorithms) do
   library[k] = v
end

return library
