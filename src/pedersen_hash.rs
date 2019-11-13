use ff::{Field, PrimeField, PrimeFieldRepr};
use jubjub::*;

use std::slice;
use std::convert::TryInto;

#[derive(Copy, Clone)]
pub enum Personalization {
    NoteCommitment,
    MerkleTree(usize),
    None,
}

impl Personalization {
    pub fn get_bits(&self) -> Vec<bool> {
        match *self {
            Personalization::None => Vec::new(),
            Personalization::NoteCommitment => vec![true, true, true, true, true, true],
            Personalization::MerkleTree(num) => {
                assert!(num < 63);

                (0..6).map(|i| (num >> i) & 1 == 1).collect()
            }
        }
    }
}

pub fn pedersen_hash<E, I>(
    personalization: Personalization,
    bits: I,
    params: &E::Params,
) -> edwards::Point<E, PrimeOrder>
where
    I: IntoIterator<Item = bool>,
    E: JubjubEngine,
{
    let mut bits = personalization
        .get_bits()
        .into_iter()
        .chain(bits.into_iter());

    let mut result = edwards::Point::zero();
    let mut generators = params.pedersen_hash_exp_table().iter();

    loop {
        let mut acc = E::Fs::zero();
        let mut cur = E::Fs::one();
        let mut chunks_remaining = params.pedersen_hash_chunks_per_generator();
        let mut encountered_bits = false;

        // Grab three bits from the input
        while let Some(a) = bits.next() {
            encountered_bits = true;

            let b = bits.next().unwrap_or(false);
            let c = bits.next().unwrap_or(false);

            // Start computing this portion of the scalar
            let mut tmp = cur;
            if a {
                tmp.add_assign(&cur);
            }
            cur.double(); // 2^1 * cur
            if b {
                tmp.add_assign(&cur);
            }

            // conditionally negate
            if c {
                tmp.negate();
            }

            acc.add_assign(&tmp);

            chunks_remaining -= 1;

            if chunks_remaining == 0 {
                break;
            } else {
                cur.double(); // 2^2 * cur
                cur.double(); // 2^3 * cur
                cur.double(); // 2^4 * cur
            }
        }

        if !encountered_bits {
            break;
        }

        let mut table: &[Vec<edwards::Point<E, _>>] =
            &generators.next().expect("we don't have enough generators");
        let window = params.pedersen_hash_exp_window_size();
        let window_mask = (1 << window) - 1;

        let mut acc = acc.into_repr();

        let mut tmp = edwards::Point::zero();

        while !acc.is_zero() {
            let i = (acc.as_ref()[0] & window_mask) as usize;

            tmp = tmp.add(&table[0][i], params);

            acc.shr(window);
            table = &table[1..];
        }

        result = result.add(&tmp, params);
    }

    result
}

pub fn pedersen_hash_with_precomp<E, I>(
    personalization: Personalization,
    bits: I,
    params: &E::Params,
) -> edwards::Point<E, PrimeOrder>
where
    I: IntoIterator<Item = bool>,
    E: JubjubEngine,
{
    let mut bits = personalization
        .get_bits()
        .into_iter()
        .chain(bits.into_iter());

    let mut result = edwards::Point::zero();
    let mut generators = params.pedersen_hash_exp_table_precomp().iter();

    loop {
        let mut acc = E::Fs::zero();
        let mut cur = E::Fs::one();
        let mut chunks_remaining = params.pedersen_hash_chunks_per_generator();
        let mut encountered_bits = false;

        // Grab three bits from the input
        while let Some(a) = bits.next() {
            encountered_bits = true;

            let b = bits.next().unwrap_or(false);
            let c = bits.next().unwrap_or(false);

            // Start computing this portion of the scalar
            let mut tmp = cur;
            if a {
                tmp.add_assign(&cur);
            }
            cur.double(); // 2^1 * cur
            if b {
                tmp.add_assign(&cur);
            }

            // conditionally negate
            if c {
                tmp.negate();
            }

            acc.add_assign(&tmp);

            chunks_remaining -= 1;

            if chunks_remaining == 0 {
                break;
            } else {
                cur.double(); // 2^2 * cur
                cur.double(); // 2^3 * cur
                cur.double(); // 2^4 * cur
            }
        }

        if !encountered_bits {
            break;
        }

        let mut table: &[Vec<edwards::Point<E, _>>] =
            &generators.next().expect("we don't have enough generators");
        let window = params.pedersen_hash_exp_window_size();
        let window_mask = (1 << window) - 1;

        let mut acc = acc.into_repr();

        let mut tmp = edwards::Point::zero();
        let mut tmp_bytes_mut = unsafe {
            slice::from_raw_parts_mut((&mut tmp as *mut _) as *mut u64, 16)
        };
        let mut tmp_bytes = unsafe {
            slice::from_raw_parts((&tmp as *const _) as *const u64, 16)
        };

        while !acc.is_zero() {
            let i = (acc.as_ref()[0] & window_mask) as usize;
            let p2 = unsafe {
                slice::from_raw_parts((&table[0][i] as *const _) as *const u64,
                                      16)
            };

            twisted_edwards_jubjub_add::ext_twisted_ed_add_256(
                tmp_bytes.try_into().expect("slice needs len of 16"),
                p2.try_into().expect("slice needs len of 16"),
                tmp_bytes_mut.try_into().expect("slice needs len of 16")
            );

            acc.shr(window);
            table = &table[1..];
        }

        result = result.add(&tmp, params);
    }

    result
}

#[cfg(test)]
mod test {
    use paired::bls12_381::Bls12;
    use rand::{Rng, SeedableRng, XorShiftRng};
    use super::*;

    #[test]
    fn pedersen_hash_vs_precomp() {
        let params = JubjubBls12::new_with_window_size(16);
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let personalization = Personalization::MerkleTree(31);

        for _ in 0..500000 {
           let bits = (0..510).map(|_| rng.gen::<bool>()).collect::<Vec<_>>();
           let hash_orig = pedersen_hash::<Bls12, _>(personalization, bits.clone(), &params).into_xy();
           let hash_new  = pedersen_hash_with_precomp::<Bls12, _>(personalization, bits.clone(), &params).into_xy();
           assert_eq!(hash_orig, hash_new);
        }
    }
}
