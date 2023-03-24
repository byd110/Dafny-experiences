/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "./NonNativeTypes.dfy"
include "./Contract.dfy"
include "./Token.dfy"

import opened NonNativeTypes

// datatype Msg = Msg(sender: Account, value: uint256)

// type Address = Account

class errorneous
{
  var amount0Out : real, reserve0 : real, reserve1 : real;
  var token0 : map<errorneous, real>, token1 : map<errorneous, real>;

  method swap(amount1Out : real, to : errorneous)
    requires this in token0 && this in token1
    requires token1[this] == reserve1
    requires reserve0 - amount0Out == token0[this] && reserve0 > amount0Out >= 0.0
    requires amount0Out > 0.0 && reserve1 > 0.0 && reserve0 > 0.0

    modifies this

    ensures reserve0 * reserve1 >= old(reserve0) * old(reserve1)
  {
    if(0.0 < amount1Out < token1[this])
    {
      token1 := token1[this := token1[this] - amount1Out];
      token0 := token0[this := havoc()];
      var balance0, balance1 := token0[this], token1[this];
      var amount0in : real := balance0 - (reserve0 - amount0Out);
      var balance0Adj : real := balance0 * 10000.0 - amount0in * 22.0;
      if(balance0Adj * balance1 >= reserve0 * reserve1 * 1000.0)
      {
        reserve0, reserve1 := balance0, balance1;
      }
    }
  }
}

function method {:extern} havoc() : real
  ensures havoc() > 0.0
