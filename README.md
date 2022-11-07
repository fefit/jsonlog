# jsonlog

A command line tool that simplifies parsing json data type logs.

## usage

```bash
# json logs
cat <<EOT > json.log
{ "name": "json", "value": 1 }
{ "name": "log", "value": 3 }
{ "name": "demo", "value": 5}
EOT
# use --disp(-d for short) to define the data output template
# use '{}' curly braces to wrap output field expression
jsonlog json.log -d '{name}\t{value + 1}'
# ---------output---------
# json  2
# log	  4
# demo  6
# ------------------------
# use the pipe operator to get stdin as input
cat json.log | jsonlog -d '{name}\t{value + 1}'
# use --index(-i for short) to jump lines
# use --num(-n for short) to limit lines
jsonlog json.log -d '{name}' -i 1 -n 1
# ---------output---------
# log
# ------------------------
# use the --cond(-c for short) to filter rows that satisfy the condition
jsonlog json.log -d '{name}' -c 'value > 1'
# ---------output---------
# log
# demo
# ------------------------
# use --out-sep(-j for short) to change the default output seperator
jsonlog json.log -d '{name}' -c 'value > 1' -j '\t'
# ---------output---------
# log	demo
# ------------------------

# error handling
echo '{name: "error"}' >> json.log
jsonlog json.log -d '{name}' -e '{data::error}'
# ---------output---------
# json
# log
# demo
# key must be a string at line 1 column 2
# ------------------------
# output only error lines
jsonlog json.log -e '{data::row}'
# ---------output---------
# 4
# ------------------------
```

# installation

## On Mac

```bash
# use homebrew
brew tap fefit/jsonlog
brew install jsonlog
# donwload the binary file
curl -OL https://github.com/fefit/jsonlog/releases/download/v0.1.0/jsonlog-mac-0.1.0.tar.gz -o jsonlog.tar.gz
tar -zxvf jsonlog.tar.gz
mv jsonlog /usr/local/bin
```

## On linux

```bash
curl -OL https://github.com/fefit/jsonlog/releases/download/v0.1.0/jsonlog-linux-0.1.0.tar.gz -o jsonlog.tar.gz
tar -zxvf jsonlog.tar.gz
sudo mv jsonlog /usr/local/bin
```

## cli options

| argument       | short | description                                                                                                                                                                                                                                                                                  |
| :------------- | :---- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| --disp         | -d    | The successfully parsed json data item output template, use `{}` to wrap expressions, in expression, variables with name from the json data's keys can be used.                                                                                                                              |
| --cond         | -c    | Filter the items that satisfy the condition expression.                                                                                                                                                                                                                                      |
| --err-disp     | -e    | Error data output template, the error message will be injected in the data::error variable.                                                                                                                                                                                                  |
| --off-err-cond | -o    | Do not use condition filter for error data item.                                                                                                                                                                                                                                             |
| --sep          | -s    | The seperator of the input json data logs, default is `\n`, one log per line, if it's not `\n`, it will parsed as a regex.                                                                                                                                                                   |
| --out-sep      | -j    | The seperator of the output data, default is `\n`                                                                                                                                                                                                                                            |
| --sep-max      | -m    | If the `--sep` is not `\n`, it will use it as a regex to split the input json data logs, this parameter specifies the maximum number of characters that can be matched by the split regex, e.g. `--sep '\n\t'`, the `\n\t` will match a fixed two charcters, then you can set `--sep-max 2`. |
| --index        | -i    | The data item starting number index, default `0`, use this argument to jump the starting lines                                                                                                                                                                                               |
| --num          | -n    | The maximum number of the input json data log items.                                                                                                                                                                                                                                         |

## expressions

`jsonlog` uses the awesome crate [`evalexpr`](https://github.com/ISibboI/evalexpr) to provide expression support, so the builtin expression syntax and functions are supported, in addtion, some built-in data-related variables and methods are provided.

| keyword                                   | type     | --cond | --disp | --err-disp | description                                                                                                               |
| :---------------------------------------- | :------- | :----- | :----- | :--------- | :------------------------------------------------------------------------------------------------------------------------ |
| `data::has_key(string, ...string)`        | function | ✓      | ✓      | ✓          | judge if the json data item has the specified keys.                                                                       |
| `data::row`                               | variable | ✓      | ✓      | ✓          | the row number of the json data item, becareful to use only when needed, it will affect part of the parallel performance. |
| `data::error`                             | variable | x      | x      | ✓          | show the json parsing error of the error data item.                                                                       |
| `string::find(haystack, search, [index])` | function | ✓      | x      | x          | find the position of the `search` string in the `haystack`                                                                |

More functions please see the crate [evalexpr's README](https://github.com/ISibboI/evalexpr#builtin-functions)

## Questions & Bugs?

Welcome to report to us with issue if you meet any question or bug. [Issue](https://github.com/fefit/jsonlog/issues)

## License

[MIT License](./LICENSE).
