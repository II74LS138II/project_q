import time
import numpy as np
from hashlib import shake_128
import secrets

# 参数配置（简化 Dilithium 实现）
N = 256
Q = 8380417
ETA = 2
BETA = 175
GAMMA = (Q - 1) // 16


def shake128_hash(message, length):
    """SHAKE-128 哈希"""
    return shake_128(message).digest(length)


def poly_uniform(seed, nonce):
    """生成随机多项式"""
    shake_input = seed + bytes([nonce])
    stream = shake128_hash(shake_input, N * 2)
    coeffs = []
    for i in range(N):
        coeff = int.from_bytes(stream[2 * i:2 * i + 2], "little") % Q
        coeffs.append(coeff)
    return np.array(coeffs)


def poly_mod(q, mod=Q):
    """将多项式取模"""
    return q % mod


# 1. 密钥生成
def keygen():
    seed = secrets.token_bytes(32)
    rho = shake128_hash(seed, 32)
    sigma = shake128_hash(seed + b'\x01', 32)
    s1 = np.random.randint(-ETA, ETA + 1, N)
    s2 = np.random.randint(-ETA, ETA + 1, N)
    A = poly_uniform(rho, 0)
    t = poly_mod(A @ s1 + s2)
    pk = (rho, t)
    sk = (s1, s2, A, sigma)
    return pk, sk


# 2. 签名生成
def sign(sk, message):
    s1, s2, A, sigma = sk
    mu = shake128_hash(sigma + message, 32)
    nonce = 0
    while True:
        y = np.random.randint(-GAMMA, GAMMA + 1, N)
        v = poly_mod(A @ y)
        c_hash = shake128_hash(mu + v.tobytes(), 32)
        c = np.frombuffer(c_hash, dtype=np.uint16) % Q
        z = y + c * s1
        if np.all(np.abs(z) <= GAMMA - BETA):
            break
        nonce += 1
    return (z, c)


# 3. 签名验证
def verify(pk, message, signature):
    rho, t = pk
    z, c = signature
    if np.any(np.abs(z) > GAMMA - BETA):
        return False
    A = poly_uniform(rho, 0)
    v = poly_mod(A @ z - c * t)
    mu = shake128_hash(rho + message, 32)
    c_prime = shake128_hash(mu + v.tobytes(), 32)
    c_check = np.frombuffer(c_prime, dtype=np.uint16) % Q
    return np.array_equal(c, c_check)


# 时间分析
def time_analysis(message, num_signatures=4):
    # 生成密钥对
    keypairs = [keygen() for _ in range(num_signatures)]
    signatures = []
    sign_times = []
    verify_times = []

    # 签名时间测量
    for pk, sk in keypairs:
        start = time.time()
        signature = sign(sk, message)
        end = time.time()
        signatures.append((pk, signature))
        sign_times.append(end - start)

    # 验证时间测量
    for pk, signature in signatures:
        start = time.time()
        is_valid = verify(pk, message, signature)
        end = time.time()
        verify_times.append(end - start)
        assert is_valid, "验证失败！"

    return sign_times, verify_times


# 测试
if __name__ == "__main__":
    message = b"Hello, Dilithium!"  # 待签名消息

    # 分析签名和验证时间
    sign_times, verify_times = time_analysis(message, num_signatures=4)

    # 输出结果
    print("签名时间 (秒):", sign_times)
    print("平均签名时间 (秒):", sum(sign_times) / len(sign_times))
    print("验证时间 (秒):", verify_times)
    print("平均验证时间 (秒):", sum(verify_times) / len(verify_times))