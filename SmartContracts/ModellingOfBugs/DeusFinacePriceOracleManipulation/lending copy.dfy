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

  var collateral : real;
  var token1 : real;
  var token2 : real;
  ghost var inv : real;
  // var reservetime : real;
  // var lastprice1 : nat;
  // var lastprice2 : nat;
  // var positive : bool;

  function method customized_price (data1 : real, data2 : real) : real
    requires data2 != 0.0
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

  predicate valid()
    reads this
  {
    token1 * token2 == inv
  }

  method mutate () returns (data1m : real, data2m : real)
    requires valid()
    requires token2 != 0.0

    // reads this
    modifies this

    ensures data2m != 0.0
    ensures valid()
  {
    var m : real := mut();
    data1m := token1 * m;
    data2m := token2 / m;
    // calc
    // {
    //   inv;
    //   token1 * token2;
    //   token1 * m * token2 / m;
    //   (token1 * m) * (token2 / m);
    //   data1m * data2m;
    //   inv;
    // }
    update(data1m, data2m);
  }

  method update (tok1 : real, tok2 : real)
    requires valid()
    requires tok1 * tok2 == inv
    requires tok2 != 0.0

    modifies this

    ensures valid()
    ensures token2 != 0.0
  {
    token1 := tok1;
    token2 := tok2;
  }

  // predicate mutate(data1: nat, data2 : nat, r1: Try<()>, amount :nat)
  // {
  //   transactions(amount, data1 * mutation(), data2 / mutation()) == r1
  // }

  method transactions(amount : real, data1 : real, data2 : real) returns (r1: Try<()>, price : real, mutationPrice : real)
    requires valid()
    requires data2 != 0.0

    modifies this

    ensures  r1.Revert? ==>  mutationPrice * collateral < amount
    // ensures price ==

  {
    // var data1:real, data2:real := inquire();
    assume(data1 * data2 == inv);
    update(data1, data2);
    collateral := havoc();
    price := customized_price(data1,data2);
    if (price * collateral < amount)
    {
      r1 := Revert();
      var mdata1 : real, mdata2 : real;
      assert(token2 != 0.0);
      mdata1, mdata2 := mutate();
      mutationPrice := customized_price(mdata1,mdata2);
    }
    else
    {
      r1 := Success(());
      mutationPrice := 0.0;
    }
  }

  // method inquire() returns (data1 : real, data2 : real)
  // requires valid()

  // ensures valid()
  // {
    
  // }

  // lemma mutation(data1 : real, data2: real)
  //   requires m != 0.0
  //   ensures data1 * data2 == (data1 * m) * (data2 / m)
}

method {:extern} havoc() returns (a: real)
  ensures a != 0.0

method {:extern} mut() returns (a: real)
  ensures 0.0 < a < 10.0
