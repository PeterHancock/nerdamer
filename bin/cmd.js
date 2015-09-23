#!/usr/bin/env node

var nerdamer = require('../nerdamer.core'),
    args = require('minimist')(process.argv.slice(2));

if (!args._.length) {
    throw "Error: No expression given"
}

var expression = nerdamer(args._[0], args, args._.slice(1));

console.log(args.eval ? expression.evaluate() : expression.text());
