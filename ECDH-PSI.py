import hashlib # For hashing and commitments
import math # For Bloom filter size calculations
import secrets # For secure random number generation
import time # For measuring execution time
from dataclasses import dataclass # For structured party representation
from typing import Dict, Iterable, List, Set, Tuple

# ECDSA library for elliptic curve operations
from ecdsa import NIST256p
from ecdsa.ellipticcurve import Point


# Parameters
CURVE = NIST256p.curve
G = NIST256p.generator
n = NIST256p.order  
HASH_NAME = "sha384" 



# Utility functions for hashing, point encoding, and key generation
def hash_bytes(data: bytes) -> bytes:
    """Return digest bytes using the selected hash."""
    h = hashlib.new(HASH_NAME)
    h.update(data)
    return h.digest()

def hash_text(text: str) -> bytes:
    """Hash a string into bytes."""
    return hash_bytes(text.encode("utf-8"))

def hash_to_scalar(text: str, modulus: int) -> int:
    """Map text -> scalar in [1, modulus-1]."""
    value = int.from_bytes(hash_text(text), "big") % modulus
    return value if value != 0 else 1

def hash_to_point(text: str) -> Point:
    """
    Map an element x to a curve point H(x) by hashing to a scalar h
    and computing h*G.
    """
    h = hash_to_scalar(text, n)
    return h * G

def encode_point(point: Point) -> bytes:
    """
    Serialize a point into bytes for hashing/comparison.
    (NIST256p uses 32 bytes for coordinates)
    """
    x_bytes = point.x().to_bytes(32, "big")
    y_bytes = point.y().to_bytes(32, "big")
    return b"\x04" + x_bytes + y_bytes

def point_commitment(point: Point) -> str:
    """
    Commitment = Hash(serialized_point).
    """
    return hashlib.new(HASH_NAME, encode_point(point)).hexdigest()

def random_private_key() -> int:
    """
    Generate private scalar in [1, n-1].
    """
    return secrets.randbelow(n - 1) + 1


# Bloom Filter Implementation
class BloomFilter:
    def __init__(self, size: int, num_hashes: int) -> None:
        self.size = size
        self.num_hashes = num_hashes
        self.bits = [0] * size

    def _positions(self, item: str) -> List[int]:
        positions = []
        for i in range(self.num_hashes):
            data = f"{i}:{item}".encode("utf-8")
            digest = hashlib.sha256(data).digest()
            pos = int.from_bytes(digest, "big") % self.size
            positions.append(pos)
        return positions

    def add(self, item: str) -> None:
        for pos in self._positions(item):
            self.bits[pos] = 1

    def __contains__(self, item: str) -> bool:
        return all(self.bits[pos] == 1 for pos in self._positions(item))

# Build Bloom filter from items with calculated size and hash count based on desired false positive rate.
def build_bloom_filter(items: Iterable[str], false_positive_rate: float = 0.01) -> BloomFilter:
    items = list(items)
    items_count = max(len(items), 1)

    m = max(8, int(-(items_count * math.log(false_positive_rate)) / (math.log(2) ** 2)))
    k = max(1, int((m / items_count) * math.log(2)))

    bloom = BloomFilter(size=m, num_hashes=k)
    for item in items:
        bloom.add(item)
    return bloom


# Party model
@dataclass
class Party:
    name: str
    private_set: Set[str]
    private_key: int

    def _get_blinded_key(self) -> int:
        """
        Apply Scalar Blinding to protect against Side-Channel Attacks.
        k_blind = k + r * n
        r is a random value > 128 bits (As justified by Schindler & Wiemers)
        """
        r = secrets.randbits(130)
        return self.private_key + (r * n)
        

    def first_computation(self, items: Iterable[str]) -> Dict[str, Point]:
        """
        Compute aH(x) or bH(y) using the blinded private key.
        """
        result: Dict[str, Point] = {}
        blinded_key = self._get_blinded_key()
        for item in items:
            Hx = hash_to_point(item)
            result[item] = blinded_key * Hx
        return result

    def commitments(self, transformed: Dict[str, Point]) -> Dict[str, str]:
        """
        Compute Hash(aH(x)) or Hash(bH(y)).
        """
        return {item: point_commitment(pt) for item, pt in transformed.items()}

    def verify_commitments(self, transformed: Dict[str, Point], commitments: Dict[str, str]) -> bool:
        """
        Verify received commitments.
        """
        for item, pt in transformed.items():
            expected = point_commitment(pt)
            received = commitments.get(item)
            if received != expected:
                return False
        return True

    def double_computation(self, received_points: Dict[str, Point]) -> Dict[str, Point]:
        """
        Compute a(bH(y)) or b(aH(x)) using the blinded private key.
        """
        blinded_key = self._get_blinded_key()
        return {item: blinded_key * pt for item, pt in received_points.items()}


# ECDH-PSI Protocol
def ecdh_psi_protocol(set_a: Set[str], set_b: Set[str]) -> Tuple[Set[str], Dict[str, object]]:
    """
    Educational prototype matching your diagram:
    1. A builds Bloom filter from S_A and sends it to B.
    2. B filters S_B -> S'_B.
    3. A computes aH(x), x in S_A.
    4. B computes bH(y), y in S'_B.
    5. Both compute commitments.
    6. Verify commitments.
    7. A computes a(bH(y)).
    8. B computes b(aH(x)).
    9. Compare results and output S_A ∩ S_B.
    """

    # Parties
    A = Party(name="A", private_set=set_a, private_key=random_private_key())
    B = Party(name="B", private_set=set_b, private_key=random_private_key())

    # Step 1: A builds Bloom filter from S_A
    bloom_a = build_bloom_filter(A.private_set)

    # Step 2: B filters S_B using Bloom filter -> S'_B
    filtered_b = {item for item in B.private_set if item in bloom_a}

    # Step 3: A computes aH(x), x ∈ S_A
    A_first = A.first_computation(A.private_set)

    # Step 4: B computes bH(y), y ∈ S'_B
    B_first = B.first_computation(filtered_b)

    # Step 5: commitments
    A_commit = A.commitments(A_first)
    B_commit = B.commitments(B_first)

    # Step 6: verify commitments
    if not B.verify_commitments(A_first, A_commit):
        raise ValueError("Abort: A's commitments are invalid.")
    if not A.verify_commitments(B_first, B_commit):
        raise ValueError("Abort: B's commitments are invalid.")

    # Step 7: A computes a(bH(y))
    A_double = A.double_computation(B_first)

    # Step 8: B computes b(aH(x))
    B_double = B.double_computation(A_first)

    # Step 9: compare results
    A_double_encoded = {item: encode_point(pt) for item, pt in A_double.items()}
    B_double_encoded = {item: encode_point(pt) for item, pt in B_double.items()}

    common_encodings = set(A_double_encoded.values()) & set(B_double_encoded.values())

    intersection_from_a = {item for item, enc in B_double_encoded.items() if enc in common_encodings}
    intersection_from_b = {item for item, enc in A_double_encoded.items() if enc in common_encodings}

    intersection = intersection_from_a & intersection_from_b

    debug_info = {
        "curve": "NIST256p",
        "hash": HASH_NAME,
        "A_private_key": A.private_key,
        "B_private_key": B.private_key,
        "S_A": A.private_set,
        "S_B": B.private_set,
        "S_B_filtered": filtered_b,
        "A_commitments": A_commit,
        "B_commitments": B_commit,
        "A_first_count": len(A_first),
        "B_first_count": len(B_first),
        "A_double_count": len(A_double),
        "B_double_count": len(B_double),
    }

    return intersection, debug_info


# Example run
if __name__ == "__main__":
    
    # Sample datasets for A and B with some overlap and some unique items.
    S_A = {
        "Waad", "Fahad", "Noura", "Badr", "Amal", "Hanaa", "Adel", "George", 
        "Reem", "Jihan", "Layal", "Salman", "Haneen", "Khalid", "Sara", 
        "Jawad", "Ali", "Hasan", "Layan", "Joud", "Sultan", "Majed", 
        
        
        "Jana", "Shahad", "Yousef", "Mohammed", "Omar", "Lina", "Abdulaziz", 
        "Sarah", "Banan", "Tariq", "Saud", "Nayef", "Ziyad", "Thamer", "Yasser", 
        "Saleh", "Hussain", "Turki", "Talal", "Sami", "Wael", "Qusai", "Hatem", 
        "Bassam", "Firas", "Raed", "Moath", "Muhannad", "Nader", "Osama", "Waleed", 
        "Abeer", "Afnan", "Ahlam", "Alyaa", "Amani", "Amina", 
        "Anfal", "Areej", "Asalah", "Atheer", "Azizah", "Dania", "Dina", "Eman","Fadwa",
          "Faten", "Ghada", "Hala", "Hanan", "Hind", "Huda"
    }

    S_B = {
        "Waad", "Fahad", "Noura", "Badr", "Amal", "Hanaa", "Adel", "George", 
        "Reem", "Jihan", "Layal", "Salman", "Haneen", "Khalid", "Sara", 
        "Jawad", "Ali", "Hasan", "Layan", "Joud", "Sultan", "Majed", 
       
        
        "Asma", "Dana", "Danah", "Refal", "Fay", "Bayan", "Rasha", "Rawan", 
        "Rema", "Rahaf", "Hala", "Yara", "Lama", "Ghadeer", "Maha", "Samar", 
        "Abdulrahman", "Nour", "Chayan", "Kamal", "Kayan", "Najwa", "Noha", 
        "Noud", "Raghad", "Rana", "Rania", "Razan", "Reham", "Ruba", "Saeed", 
        "Saad", "Mansour", "Mishaal", "Anas", "Tarek", "Ahmad", "Ibrahim", 
        "Mahmoud", "Mustafa", "Abbas", "Hamza", "Bilal", "Zaid", "Taha", 
        "Younis", "Idris", "Ayoub", "Yaqoub", "Issa", "Mousa", "Haroun", 
        "Sulaiman", "Dawoud", "Zakariya", "Yahya", "Ayman", "Amjad", "Anwar", 
        "Akram", "Ashraf", "Adham", "Iyad", "Bahaa", "Taj", "Jalal", "Jamal", 
        "Husam", "Hazem", "Diya", "Rabea", "Zahir", "Siraj", "Shafiq", "Safwan","Rakan",
          "Rayan", "Nawaf","Feras", "Fahd"
    }

    # Measure execution time
    start_time = time.time()
    intersection, info = ecdh_psi_protocol(S_A, S_B)
    end_time = time.time()
    execution_time = end_time - start_time

    # Output results and debug info
    print("=== ECDH-PSI Result ===")
    print("Intersection:", intersection)
    print("\n=== Protocol Flow Info ===")
    print(f"Curve used: {info['curve']}")
    print(f"Hash used: {info['hash']}")
    print(f"A's Original Dataset size: {len(info['S_A'])}")
    print(f"B's Original Dataset size: {len(info['S_B'])}")
    print(f"B's Dataset size AFTER Bloom Filter: {len(info['S_B_filtered'])}")
    print(f"Side-Channel Protection: Active (Scalar Blinding > 128 bits)")
    # Calculate Bloom filter reduction and false positives
    reduction = (1 - len(info['S_B_filtered']) / len(info['S_B'])) * 100
    print(f"Bloom Filter Reduction: {reduction:.2f}%")
    # False positives are items in S_B_filtered that are not in the intersection.
    false_positives = len(info['S_B_filtered']) - len(intersection)
    print(f"False Positives: {false_positives}")
    print(f"Execution Time: {execution_time:.4f} seconds")


    

