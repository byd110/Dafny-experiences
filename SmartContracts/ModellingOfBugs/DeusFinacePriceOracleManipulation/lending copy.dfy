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
  // include "./Token.dfy"

import opened NonNativeTypes

datatype Msg = Msg(sender: Account, value: uint256)
datatype Try<T> = Success(v: T) | Revert()

type Address = Account

class LendingContract  {

  var collateral : nat;
  // var reservetime : real;
  // var lastprice1 : nat;
  // var lastprice2 : nat;
  // var positive : bool;

  function method customized_price (data1 : nat, data2 : nat) : nat
    requires data2 != 0
  {
    data1 / data2
  }

  // function method customized_price2 (data1 : nat, data2 : nat) : nat
  //   requires data2 != 0
  //   requires reservetime.Floor >= 0
  //   reads this
  // {
  //   (((lastprice1 as real - data1 as real)  * reservetime + lastprice1 as real)/((lastprice2 as real - data2 as real)  * reservetime + lastprice2 as real)).Floor as nat
  // }

  method getdata1() returns (data1 : nat)
    ensures data1 != 0
  {data1 := havoc();}

  method getdata2() returns (data2 : nat)
    ensures data2 != 0
  {data2 := havoc();}

  // predicate mutate(data1: nat, data2 : nat, r1: Try<()>, amount :nat)
  // {
  //   transactions(amount, data1 * mutation(), data2 / mutation()) == r1
  // }

  method transactions(amount : nat, data1 : nat, data2 : nat) returns (r1: Try<()>, price : nat)
    requires data2 != 0

    modifies this

    ensures  r1.Revert? ==> forall m : nat :: 0 < m < 10 ==> customized_price(data1* m,(if data2/m == 0 then 1 else data2/m)) * collateral < amount

  {
    collateral := havoc();
    price := customized_price(data1,data2);
    if (price * collateral < amount)
    {
      r1 := Revert();

    }
    else
    {r1 := Success(());}
  }
}

method {:extern} havoc() returns (a: nat)
  ensures a != 0