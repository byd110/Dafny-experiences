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

// include "./NonNativeTypes.dfy"
// include "./Contract.dfy"
// include "./Token.dfy"

// import opened NonNativeTypes

// datatype Msg = Msg(sender: Account, value: uint256)

// type Address = Account
class address {
  var m_address: nat;
}
class errorneous
{
  var k : nat; //product invariant
  var m_address: address;
  var amount0Out : nat, reserve0 : nat, reserve1 : nat;
  var token0 : map<address, nat>, token1 : map<address, nat>;

  method swap(amount1Out : nat, to : address)
    requires this.m_address in token0 && this.m_address in token1
    requires to in token0 && to in token1
    requires token1[this.m_address] ==  reserve1
    requires reserve0 - amount0Out == token0[this.m_address]
    requires amount0Out == 0 //since we don't understand what this var is, we set it to 0.
    requires amount1Out <= token1[this.m_address]
    requires reserve1 > 0 && reserve0 > 0
    requires reserve0 * reserve1 == k
    requires amount1Out < reserve1

    modifies this

    ensures reserve0 * reserve1 >= old(reserve0) * old(reserve1)
  {
    token1 := transfer(token1, amount1Out, to,  this.m_address);
    token0 := uniswapCall(to);
    var balance0, balance1 := token0[this.m_address], token1[this.m_address];
    var amount0in : nat := if reserve0 - amount0Out > balance0 then 0 else balance0 - (reserve0 - amount0Out); /*in smart contract, the negative assignment to a uint variable will assign the variable to 0.*/
    var balance0Adj : nat := balance0 * 10000 - amount0in * 22; 
    if(balance0Adj * balance1 >= reserve0 * reserve1 * 1000)
    {reserve0, reserve1 := balance0, balance1;}
  }

  method uniswapCall(to: address) returns (newt : map<address, nat>)
    requires to in token0 && this.m_address in token0
    requires this.m_address in token1
    // requires t[to] >= amount
    // modifies this
    ensures to in token0 && this.m_address in token0
    ensures this.m_address in newt
    ensures reserve0 == old(reserve0) && reserve1 == old(reserve1)
  {
    var h : nat := havoc();
    assume (token0[to] >= h);
    newt := transfer(token0, h, this.m_address, to);
  }

  method transfer(t:map<address, nat> , amount:nat, to:address, from: address) returns (newt : map<address, nat>)
    requires to in t && from in t
    requires t[from] >= amount
    ensures from in newt && to in newt
    // ensures from != to ==> newt[from] == old(t)[from] - amount 
  {
    newt := t[from := t[from] - amount];
    newt := newt[to := t[to] + amount];
  }
  constructor(a: address)
  {
    m_address := a;
  }
}


function method {:extern} havoc() : nat
  ensures havoc() > 0

// class errorneous
// {
//   var amount0Out : real, reserve0 : real, reserve1 : real;
//   var token0 : map<errorneous, real>, token1 : map<errorneous, real>;

//   method swap(amount1Out : real, to : errorneous)
//     requires this in token0 && this in token1
//     requires token1[this] == reserve1
//     requires reserve0 - amount0Out == token0[this] && reserve0 > amount0Out >= 0.0
//     requires amount0Out > 0.0 && reserve1 > 0.0 && reserve0 > 0.0

//     modifies this

//     ensures reserve0 * reserve1 >= old(reserve0) * old(reserve1)
//   {
//     if(0.0 < amount1Out < token1[this])
//     {
//       token1 := token1[this := token1[this] - amount1Out];
//       token0 := token0[this := havoc()];
//       var balance0, balance1 := token0[this], token1[this];
//       var amount0in : real := balance0 - (reserve0 - amount0Out);
//       var balance0Adj : real := balance0 * 10000.0 - amount0in * 22.0;
//       if(balance0Adj * balance1 >= reserve0 * reserve1 * 1000.0)
//       {
//         reserve0, reserve1 := balance0, balance1;
//       }
//     }
//   }
// }

// function method {:extern} havoc() : real
//   ensures havoc() > 0.0