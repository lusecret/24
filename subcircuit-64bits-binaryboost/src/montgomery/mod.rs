#![allow(dead_code)]
#![allow(non_snake_case)]
use rand_core::{CryptoRng, RngCore};

const Q: u64 = 1945555039024054273;
const QP: u64 = 1945555039024054271;
const R2: u64 = 269548777697434221;
const ONE: u64 = 936748722493063159;

// 2^0, 2^1, ..., 2^{31}
pub const POW_TWO: [u64; 32] = [
  936748722493063159,
  1873497444986126318,
  1801439850948198363,
  1657324662872342453,
  1369094286720630633,
  792633534417206993,
  1585267068834413986,
  1224979098644773699,
  504403158265493125,
  1008806316530986250,
  72057594037918227,
  144115188075836454,
  288230376151672908,
  576460752303345816,
  1152921504606691632,
  360287970189328991,
  720575940378657982,
  1441151880757315964,
  936748722490577655,
  1873497444981155310,
  1801439850938256347,
  1657324662852458421,
  1369094286680862569,
  792633534337670865,
  1585267068675341730,
  1224979098326629187,
  504403157629204101,
  1008806315258408202,
  72057591492762131,
  144115182985524262,
  288230365971048524,
  576460731942097048,
];

// 2^{-31}
pub const INV_POW_OF_TWO: u64 = 8589934592;

pub fn get_Q() -> u64 {
  Q
}

pub fn mont_one() -> u64 {
  ONE
}

pub fn mont_mul_mod(x: u64, y: u64) -> u64 {
  let xy: u128 = (x as u128) * (y as u128);

  let c0: u64 = xy as u64;
  let c1: u64 = (xy >> 64) as u64;

  let m: u128 = (c0 as u128) * (QP as u128) & 0xffff_ffff_ffff_ffff;
  let mn: u128 = m * (Q as u128);
  let mut m1: u64 = (mn >> 64) as u64;

  if c0 != 0 {
    m1 += 1;
  };

  let mut r: u64 = c1 + m1;
  if r > Q {
    r = r - Q;
  }
  r
}

pub fn enter_mont(x: u64) -> u64 {
  mont_mul_mod(x, R2)
}

pub fn back_from_mont(x: u64) -> u64 {
  mont_mul_mod(x, 1)
}

pub fn mul_mod(x: u64, y: u64) -> u64 {
  let xm = enter_mont(x);
  let ym = enter_mont(y);

  let xym = mont_mul_mod(xm, ym);

  back_from_mont(xym)
}

pub fn random64_mod<Rng: RngCore + CryptoRng>(rng: &mut Rng) -> u64 {
  let random_number: u64 = rng.next_u64();
  random_number % Q
}

pub fn mont_accumu_mul(x: &[u64]) -> u64 {
  let m = ONE;

  x.iter().cloned().fold(m, |acc, val| mont_mul_mod(acc, val))
}

// compute: a_prime = a + alpha*x
pub fn compute_aprime(a_vec: &Vec<u64>, alpha_vec: &Vec<u64>, x: u64) -> Vec<u64> {
  let xm: u64 = enter_mont(x);
  a_vec
    .into_iter()
    .zip(alpha_vec)
    .map(|(a, alpha)| {
      let am = enter_mont(*a);
      let alpham = enter_mont(*alpha);
      let alphax = mont_mul_mod(alpham, xm);
      back_from_mont(am + alphax)
    })
    .collect()
}

fn compute_pow(a: u64, exp: u64) -> u64 {
  let mut result = ONE;
  let mut base = enter_mont(a);
  let mut exponent = exp;
  while exponent > 0 {
      if exponent & 1 == 1 {
          result = mont_mul_mod(result, base);
      }
      base = mont_mul_mod(base, base);
      exponent = exponent >> 1;
  }
  back_from_mont(result)
}

pub fn inv(a: u64) -> u64 {
  compute_pow(a,  Q - 2)
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;

  #[test]
  fn test_mont() {
    let total: u32 = 1024;
    let mut csprng: OsRng = OsRng;

    for _ in 0..total {
      let a: u64 = random64_mod(&mut csprng);
      let ar: u64 = enter_mont(a);
      let act_a: u64 = back_from_mont(ar);

      assert_eq!(a, act_a);
    }

    println!("case success");
  }

  #[test]
  fn test_pow() {
    let a: u64 = 945555039024054273;

    let a_inv: u64 = inv(a);

    println!("a_inv = {:?}", a_inv);

    let r: u64 = mul_mod(a, a_inv);
    assert_eq!(r, 1);
  }

  #[test]
  fn test_mont_accum_mul() {
    const NUM_COUNT: usize = 1024;

    let exp: u64 = 1067354557705520127;

    let mut numbers = Vec::with_capacity(NUM_COUNT);
    let mut current_number = 1845555039024054203;
    for _ in 0..NUM_COUNT {
      numbers.push(current_number);
      current_number += 4000000;
    }

    let mut montdatas = Vec::with_capacity(NUM_COUNT);
    for i in 0..NUM_COUNT {
      montdatas.push(enter_mont(numbers[i]));
    }

    let result = mont_accumu_mul(&montdatas);
    assert_eq!(exp, back_from_mont(result));
  }

  #[test]
  fn test_mont_accum_add() {
    let acc: Vec<u64> = vec![
      1200366400900809890,
      1702035432336202261,
      1358926091749906767,
      220060218789666825,
      166853422518846306,
      1820512326895632113,
      523529462771106436,
      1735193447666617246,
      1136308116845108428,
      1285080590547972295,
      685912635425863219,
      266323692499654029,
      1939657771614208825,
      867733658296762242,
      478627121747398369,
      855810106659118496,
      1735612508957263297,
      402584881063563634,
      375236677472195465,
      1928985690349907714,
      1691137580894383175,
      957571262275242545,
      1838511543097521831,
      1683061339227952141,
      1639318425179819084,
      369554275780989740,
      697151300546565219,
      138412203783727735,
      21029186205734342,
      978336025384804849,
      656405086651261614,
      603219199492217652,
    ];
    let sum: u128 = acc.into_iter().map(|x| enter_mont(x) as u128).sum();

    let sum = (sum % (get_Q() as u128)) as u64;

    println!("{}", back_from_mont(sum));
  }
}
