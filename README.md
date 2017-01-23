# SystemVerilog support for VSCode [![Build Status](https://travis-ci.org/mshr-h/vscode-systemverilog-support.svg?branch=master)](https://travis-ci.org/mshr-h/vscode-systemverilog-support)
SystemVerilog support based on [https://github.com/al8/sublimetext-Verilog](https://github.com/al8/sublimetext-Verilog) SumblieText package.

## Features
### Done
- Syntax highlighting for `.sv` `.SV` files
- Snippets for:
    - **Blocks:** `always_ff`, `always_comb`, `module`, `initial`, `function`
    - **Conditional blocks:** `if`, `while`, `for`
    - **Declaration:** `parameter`, `function`
    - **Pre-build:** `include`, `define`
    - **Special:**
        - `paramod` for module with parameters
        - `begin` to generate begin and end pair

### Known bug
- `begin ... end` bracket matching not supported

## GitHub repos
[mshr-h/vscode-systemverilog-support](https://github.com/mshr-h/vscode-systemverilog-support)

## Contributing
1. Fork it ( [https://github.com/mshr-h/vscode-systemverilog-support](https://github.com/mshr-h/vscode-systemverilog-support) )
2. Create your feature branch (`git checkout -b my-new-feature`)
3. Commit your changes (`git commit -am 'Add some feature'`)
4. Push to the branch (`git push origin my-new-feature`)
5. Create a new Pull Request

## See also
[https://marketplace.visualstudio.com/items/mshr-h.SystemVerilog](https://marketplace.visualstudio.com/items/mshr-h.SystemVerilog)
