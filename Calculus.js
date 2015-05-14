(function() {
    var core = nerdamer.getCore(),
        _ = core.PARSER,
        format = core.Utils.format,
        isSymbol = core.Utils.isSymbol,
        isNumericSymbol = core.Utils.isNumericSymbol,
        FN = core.groups.FN,
        Symbol = core.Symbol,
        text = core.Utils.text,
        inBrackets = core.Utils.inBrackets,
        N = core.groups. N,
        S = core.groups.S,
        FN = core.groups.FN,
        PL = core.groups.PL,
        CP = core.groups.CP,
        CB = core.groups.CB,
        EX = core.groups.EX;
    var __ = core.Calculus = {
        version: '1.1.2',
        sum: function(fn, index, start, end) {
            if(!(index.group === core.groups.S)) throw new Error('Index must be symbol. '+text(index)+' provided');
            index = index.value;
            var retval;
            if(core.Utils.isNumericSymbol(start) && core.Utils.isNumericSymbol(end)) {
                start = start.multiplier;
                end = end.multiplier;

                var variables = core.Utils.variables(fn);
                if(variables.length === 1 && index === variables[0]) {
                    var f = core.Utils.build(fn);
                    retval = 0;
                    for(var i=start; i<=end; i++) {
                        retval += f.call(undefined, i);
                    }
                }
                else {
                    var f = fn.text(),
                        subs = {'~': true}, //lock subs
                    retval = new core.Symbol(0);

                    for(var i=start; i<=end; i++) {
                        subs[index] = new Symbol(i); 
                        retval = _.add(retval, _.parse(f, subs)); //verrrrryyy sllloooowww
                    }
                }
            }
            else {
                retval = _.symfunction('sum',arguments);
            }

            return retval;
        },
        diff: function(symbol, wrt, nth) {
            var d = isSymbol(wrt) ? wrt.text() : wrt; 
            
            nth = isSymbol(nth) ? nth.multiplier : nth || 1;

            if(d === undefined) d = core.Utils.variables(symbol)[0];

            if(symbol.group === FN && !isSymbol(symbol.power)) {
                var a = derive(symbol);
                var b = __.diff(symbol.args[0].copy(), d); 
                symbol = _.multiply(a, b);//chain rule
            }
            else {
                symbol = derive(symbol);
            }
            
            if(nth > 1) { 
                nth--;
                symbol = __.diff(symbol, wrt, nth);
            }
            
            return symbol;
            
             // Equivalent to "derivative of the outside".
            function polydiff(symbol) { 
                if(symbol.value === d || symbol.contains(d, true)) { 
                    symbol.multiplier *= symbol.power;
                    symbol.power -= 1; 
                    if(symbol.power === 0) {
                        symbol = Symbol(symbol.multiplier);
                    }
                } 
                return symbol;
            };
            function derive(symbol) { 
                var g = symbol.group, t, a, b, cp; 

                if(g === N || g === S && symbol.value !== d) { 
                    symbol = Symbol(0);
                }
                else if(g === S) {  
                    symbol = polydiff(symbol);
                }
                else if(g === CB) { 
                    var m = symbol.multiplier;
                    symbol.multiplier = 1;
                    var retval =  _.multiply(product_rule(symbol),polydiff(symbol.copy()));
                    retval.multiplier *= m;
                    return retval;
                }
                else if(g === FN && symbol.power === 1) {
                    // Table of known derivatives
                    switch(symbol.baseName) {
                        case 'log':
                            cp = symbol.copy();
                            symbol = symbol.args[0].copy();//get the arguments

                            if( isSymbol( symbol.power ) ) {
                                symbol.power = _.multiply(symbol.power, Symbol(-1));
                            }
                            else {
                                symbol.power *= -1;
                            }
                            symbol.multiplier = cp.multiplier/symbol.multiplier; 
                            break;
                        case 'cos':
                            symbol.baseName = 'sin';
                            symbol.multiplier *= -1;
                            break;
                        case 'sin': 
                            symbol.baseName = 'cos';
                            break;
                        case 'tan':
                            symbol.baseName = 'sec';
                            symbol.power = 2;
                            break;
                        case 'sec': 
                            // Use a copy if this gives errors
                            symbol = qdiff(symbol, 'tan');
                            break;
                        case 'csc':
                            symbol = qdiff(symbol, '-cot');
                            break;
                        case 'cot':
                            symbol.baseName = 'csc';
                            symbol.multiplier *= -1;
                            symbol.power = 2;
                            break;
                        case 'asin':
                            symbol = _.parse('(sqrt(1-('+text(symbol.args[0])+')^2))^(-1)');
                            break;
                        case 'acos':
                            symbol = _.parse('-(sqrt(1-('+text(symbol.args[0])+')^2))^(-1)');
                            break;
                        case 'atan':
                            symbol = _.parse('(1+('+text(symbol.args[0])+')^2)^(-1)');
                            break;
                        case 'abs':
                            m = symbol.multiplier; 
                            symbol.multiplier = 1;
                            //depending on the complexity of the symbol it's easier to just parse it into a new symbol
                            //this should really be readdressed soon
                            b = symbol.args[0].copy();
                            b.multiplier = 1;
                            symbol = _.parse(inBrackets(text(symbol.args[0]))+'/abs'+inBrackets(text(b)));
                            symbol.multiplier = m;
                            break;
                        case 'parens':
                            symbol = Symbol(1);
                            break;
                    }
                }
                else if(g === EX || g === FN && isSymbol(symbol.power)) { 
                    var value;
                    if(g === EX) {
                        value = symbol.value;
                    }
                    else if(g === FN && symbol.contains(d)) { 
                        value = symbol.baseName + inBrackets(text(symbol.args[0]));
                    }
                    else {
                        value = symbol.value + inBrackets(text(symbol.args[0]));
                    }
                        a = _.multiply(_.parse('log'+inBrackets(value)), symbol.power.copy()); 
                        b = __.diff(_.multiply(_.parse('log'+inBrackets(value)), symbol.power.copy()), d); 
                    symbol = _.multiply(symbol, b);
                }
                else if( g === FN && symbol.power !== 1 ) { 
                    b = symbol.copy();
                    //turn b into a vanilla powerless, multiplier-less symbol
                    b.power = 1; 
                    b.multiplier = 1;
                    symbol = _.multiply(polydiff( symbol.copy(), d ), derive(b));  
                }
                else if( g === CP || g === PL ) { 
                    var result = new Symbol(0);
                    for(var x in symbol.symbols) {
                        result = _.add(result, __.diff(symbol.symbols[x].copy(), d));
                    }
                    symbol = _.multiply(polydiff(symbol.copy()), result);
                }

                symbol.updateHash();
                return symbol;
            };

            function qdiff(symbol, val, altVal) {
                return _.multiply(symbol, _.parse(val+inBrackets(altVal || text(symbol.args[0]))));
            };

            function product_rule(symbol) { 
                //grab all the symbols within the CB symbol
                var symbols = symbol.collectSymbols(), 
                    result = new Symbol(0),
                    l = symbols.length;
                //loop over all the symbols
                for(var i=0; i<l; i++) {
                    var df = __.diff(symbols[i].copy(), d);
                    for(var j=0; j<l; j++) {
                        //skip the symbol of which we just pulled the derivative
                        if(i !== j) {
                            //multiply out the remaining symbols
                            df = _.multiply(df, symbols[j].copy());
                        }
                    }
                    //add the derivative to the result
                    result = _.add(result, df);
                }
                return result; //done
            };
        },
        integral: function(symbol, ig) {
            return _.symfunction('integrate', [symbol, ig]);
        },
        integrate: function(symbol, integrand, a, b) {   
            var do_integration = function(symbol, integrand) {
                var g = symbol.group,
                    ig = text(integrand),
                    p = symbol.power;
            
                if(g === N || !symbol.contains(ig, true)) {
                    symbol = _.multiply(symbol, integrand.copy());
                }
                else { 
                    var p = symbol.power;
                    //apply rules to different groups
                    if(g === S) {
                        symbol.power+=1;
                        symbol.multiplier /= symbol.power;
                    }
                    else if(g === FN) {
                        var param = symbol.args[0];
                        if(p === 1) {
                            if(param.group === S && param.power === 1) { 
                                var r;
                                switch(symbol.baseName) {
                                    case 'cos':
                                        r = 'sin({0})';
                                        break;
                                    case 'sin':
                                        r = '-cos({0})';
                                        break;
                                    case 'tan':
                                        r = 'log(sec({0}))';
                                        break;
                                    case 'sec':
                                        r = 'log(tan({0})+sec({0}))';
                                        break;
                                    case 'csc': 
                                        r = '-log(csc({0})+cot({0}))';
                                        break;
                                    case 'cot':
                                        r = 'log(sin({0}))';
                                        break;
                                    case 'acos':
                                        r = 'x*acos(x)-sqrt(1-x^2)';
                                        break;
                                    case 'asin':
                                        r = '{0}*asin({0})+sqrt(1-{0}^2)';
                                        break;
                                    case 'atan':
                                        r = '{0}*atan({0})-log({0}^2+1)/2';
                                        break;
                                    case 'log':
                                        r = '{0}*log({0})-{0}';
                                        break;   
                                    case 'abs':
                                        r = '({0}*abs({0}))/2';
                                        break;
                                }
                            }
                        }
                        else if(p === 2) {
                            switch(symbol.baseName) {
                                case 'sec':
                                    r = 'tan({0})';
                                    break;
                                case 'csc':
                                    r = '-cot({0})';
                                    break;
                                case 'cos':
                                    r = '{1}*(0.5{0})+(0.25*sin(2*{0}))';
                                    break;
                            }
                        }
                        
                        if(r) symbol = _.parse(format(r, ig, symbol.multiplier));
                        
                        symbol.updateHash(); //make sure the hash of the symbol gets updated
                    }
                    else if(g === PL && p === 1) {
                        for(var s in symbol.symbols) do_integration(symbol.symbols[s], integrand);
                    }
                    else if(g === CB) { 
                        //integration is when of those instances where the model used shows its weaknesses
                        //we first go down the table of integrals and see what works
                        
                        var p = symbol.power; 
                        if(Math.abs(p) === 1) { 
                            // try 1/u du
                            var l = symbol.length,
                                symbols = symbol.collectSymbols();
                            for(var i=0; i<l; i++) { 
                                var u = symbols[i].copy();
                                    u.power = Math.abs(u.power);
                                var du = __.diff(u.copy(), ig),
                                    rem = new Symbol(1);
                                for(var j=0; j<l; j++) {
                                    var sym = symbols[j].copy();
                                    sym.power = Math.abs(sym.power);
                                    if(i !== j) rem = _.multiply(sym, rem);
                                }
                                rem.power *= p; //make sure the sign of the power is transferred
                                //u and du should differ only by a multiplier so let's check
                                var m = _.divide(rem, du);
                               
                                if(isNumericSymbol(m)) {
                                    return _.multiply(new Symbol(symbol.multiplier), _.multiply(_.parse('log('+u+')'), m));
                                }
                            }   
                            
                            //No? That wasn't it? Ok let's check for sec(u)tan(u)
                            u = symbol.copy();
                            u.multiplier = 1;//strip the multiplier
                            var r;
                            if(_.parse(format('sec({0})*tan({0})', ig)).equals(u)) {
                                r = 'sec({0})';
                            }
                            else if(_.parse(format('csc({0})*cot({0})', ig)).equals(u)) {
                                r = '-csc({0})';
                            }
                            
                            if(r) {
                                var new_symbol = _.parse(format(r, ig));
                                new_symbol.multiplier *= symbol.multiplier;
                                return new_symbol;
                            }
                        }      
                    }
                    else if(g === CP) {
                        //try du/a^2+u^2
                        if(p === -1) {
                            var u_sq = _.parse(ig+'^2'),
                                symbols = symbol.collectSymbols(), l=symbols.length;
                            for(var i=0; i<l; i++) {
                                var s = symbols[i];
                                if(s.equals(u_sq)) {
                                    var rem = new Symbol(0);
                                    for(var j=0; j<l; j++) {
                                        if(i !== j) rem = _.add(symbols[j].copy(), rem);
                                    }
                                    return _.parse(format('atan(({0})/sqrt({1}))/sqrt({1})', ig, rem));
                                }
                            }
                        }
                        else if(symbol.power === 1) {
                            var retval = new Symbol(0);
                            for(var s in symbol.symbols) {
                                retval = _.add(retval, do_integration(symbol.symbols[s], integrand));
                            }
                            return retval;
                        }
                        else {
                            if(p === -0.5) { 
                                //let's try du/sqrt(a^2-u^2)
                                var l = symbol.length, u_sq = _.parse(ig+'^2').negate(),
                                    symbols = symbol.collectSymbols();
                                for(var i=0; i<l; i++) {
                                    var s = symbols[i];
                                    if(s.equals(u_sq)) {
                                        var rem = new Symbol(0);
                                        for(var j=0; j<l; j++) {
                                            if(i !== j) rem = _.add(rem, symbols[j])
                                        }
                                        return _.parse(format('asin({0}/abs({1}))', ig, rem));
                                    }
                                }
                            }
                            return __.integral(symbol);
                        }
                    }
                    else if(g === EX && !isNaN(symbol.value)) {
                        if(symbol.power.power === 1) { 
                            return _.parse(format('({0})/(log({2})*{1})', symbol, symbol.power.multiplier, symbol.value));
                        }
                    }
                    else {
                        return __.integral(symbol, ig);
                    }
                }
                
                return symbol;
            };
            
            //first go through the table of integrals
            symbol = do_integration(symbol, integrand);
            
            return symbol;
        }
    };
    
    nerdamer.register([
        {
            name: 'diff',
            visible: true,
            numargs: [1,3],
            build: function(){ return __.diff; }
        },
        {
            name: 'differentiate',
            visible: true,
            numargs: [1,3],
            build: function(){ return __.diff; }
        },
        {
            name: 'sum',
            visible: true,
            numargs: 4,
            build: function(){ return __.sum; }
        },
        {
            name: 'integrate',
            visible: true,
            numargs: [2, 3], 
            build: function(){ return __.integrate; }
        }
    ]);
})();
