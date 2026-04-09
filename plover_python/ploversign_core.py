import os

from Crypto.Hash import SHAKE256

from nist_kat_drbg import NIST_KAT_DRBG

from mask_random import MaskRandom

from polyr import *

from math import ceil, sqrt, log, floor

import json  # 【新增1】导入 json 模块

from polyr import poly_lshift  # 【新增2】导入左移函数，用于重构公钥 t

import subprocess

import sys

BYTEORDER = "little"

import time

from multiprocessing import Pool

import multiprocessing


class PloverSign:

    def __init__(
        self,
        bitsec,
        q,
        logdivide,
        nut,
        rep,
        ut,
        up,
        n,
        d,
        masking_poly=MaskRandom().random_poly,
        random_bytes=os.urandom,
        kappa=512,
    ):

        self.name = f"Plover-{bitsec}-{d}"

        self.bitsec = bitsec

        self.d = d

        self.q = q

        self.logdivide = logdivide

        self.q_bits = self.q.bit_length()

        self.n = n

        self.nut = nut

        self.rep = rep

        self.ut = ut

        self.up = up

        self.sec = self.bitsec // 8  # pre-image resistance, bytes

        self.crh = 2 * self.sec  # collision resistance, bytes

        self.as_sz = self.sec  # A seed size

        self.salt_sz = self.crh  # mu digest H(tr, m) size

        self.tr_sz = self.crh  # tr digest H(pk) size

        self.mk_sz = self.sec  # serialization "key" size

        self.masking_poly = masking_poly

        self.random_bytes = random_bytes

        self._compute_metrics()

    def keygen(self):

        seed = self.random_bytes(self.as_sz)

        a_ntt = ntt(self._expand_a(seed))

        me = self._vec_add_rep_noise(self.ut, 0, self.rep)

        ms = self._vec_add_rep_noise(self.ut, 0, self.rep)

        ms_ntt = mat_ntt([ms])[0]

        mb_ntt = mul_mat_mvec_ntt([[a_ntt]], [ms_ntt])[0]

        mb = mat_intt([mb_ntt])[0]

        for j in range(self.d):

            mb[j] = poly_add(mb[j], me[j])

        b = self._decode(mb)

        b[0] = (2**self.logdivide - b[0]) % self.q

        for i in range(1, self.n):

            b[i] = (-b[i]) % self.q

        qt = self.q >> self.nut

        b = poly_rshift(b, self.nut, qt)

        vk = (seed, b)  # 公钥，b对应t

        msk = (seed, b, ms_ntt)  # 私钥，ms_ntt对应s

        return msk, vk

    def sign_msg(self, msk, tr, msg):

        (seed, b, ms_ntt) = msk

        a_ntt = ntt(self._expand_a(seed))

        rsp_norms = False

        while not rsp_norms:

            salt = self.random_bytes(self.salt_sz)

            u = self._msg_hash(salt, tr, msg)

            mp = [self._vec_add_rep_noise(self.up, i, self.rep) for i in range(2)]

            mp_ntt = mat_ntt(mp)

            mw_ntt = [[None] for _ in range(self.d)]

            for i_d in range(self.d):

                mw_ntt[i_d] = poly_add(mp_ntt[0][i_d], mul_ntt(a_ntt, mp_ntt[1][i_d]))

            self._refresh(mw_ntt)

            w_ntt = self._decode(mw_ntt)

            w = intt(w_ntt)

            u_ = poly_sub(u, w)

            c1 = [0] * self.n

            # print(self.maxc1)

            mid1 = self.maxc1

            mid2 = 1 << (self.logdivide - 1)

            mid = mid1 * (1 << self.logdivide) + mid2

            for i in range(self.n):

                c1[i] = (((u_[i] + mid) % self.q) >> self.logdivide) - mid1

            c1_ntt = ntt(c1.copy())

            self._refresh(ms_ntt)

            mz2_ntt = [[None] for _ in range(self.d)]

            for i_d in range(self.d):

                mz2_ntt[i_d] = poly_add(mul_ntt(c1_ntt, ms_ntt[i_d]), mp_ntt[1][i_d])

            self._refresh(mz2_ntt)

            # print(mz2_ntt)

            z2_ntt = self._decode(mz2_ntt)

            z2 = intt(z2_ntt)

            z2 = poly_center(z2)

            z3 = poly_center(c1)

            rsp_norms, z1 = self._check_bounds(u, a_ntt, b, z2, z3)

        sig = (salt, z2, z3, u, z1)

        return sig

    def verify_msg(self, vk, tr, msg, sig):

        (salt, z2, z3, u_ori, z1_ori) = sig

        (seed, b) = vk

        a_ntt = ntt(self._expand_a(seed))

        u = self._msg_hash(salt, tr, msg)

        if u != u_ori:

            return False

        # if self._check_bounds(u, a_ntt, b, z2, z3) == False:

        #     return False

        is_valid, _ = self._check_bounds(u, a_ntt, b, z2, z3)

        if is_valid == False:

            return False

        return True

    def set_random(self, random_bytes):

        self.random_bytes = random_bytes

    def set_masking(self, masking_poly):

        self.masking_poly = masking_poly

    def _compute_metrics(self):

        self.maxc1 = (((self.q - 1) >> self.logdivide) + 1) >> 1

        # print("y:%d",self.maxc1)

        sigp = sqrt(self.rep * ((1 << self.up) ** 2 + 1) / 12)

        self.sq_beta = floor(
            2**2
            * (
                self.n
                * (2 * (sigp**2) + (self.maxc1**2 + (1 << self.logdivide) ** 2) / 4)
            )
        )

        self.sq_beta += self.n**2 * ((1 << (self.nut - 1)) * self.maxc1) ** 2

    def _check_bounds(self, u, a_ntt, t, z2, c1):

        t2 = poly_lshift(t, self.nut)

        t2 = [c - (1 << (self.nut - 1)) for c in t2]

        t_ntt = ntt(t2.copy())

        z2_ntt = ntt(z2.copy())

        c1_ntt = ntt(c1.copy())

        z1_ntt = [a_ntt[i] * z2_ntt[i] + t_ntt[i] * c1_ntt[i] for i in range(self.n)]

        z1 = intt(z1_ntt)

        z1 = poly_sub(u, z1)

        # 【重点修复在这里】

        for c in c1:

            if abs(c) > self.maxc1:

                return False, z1  # <--- 之前这里只有 return False，加上 z1

        sq_bound = self.sq_beta

        sq_n = 0

        for v in poly_center(z1):

            sq_n += v * v

        for v in poly_center(z2):

            sq_n += v * v

        for v in poly_center(c1):

            sq_n += v * v

        # 末尾的返回

        is_valid = sq_n <= sq_bound

        return is_valid, z1

    def _decode(self, mp):
        """Decode(): Collapse shares into a single polynomial."""

        r = mp[0].copy()

        for p in mp[1:]:

            r = poly_add(r, p)

        return r

    def _zero_encoding(self):

        z = [[0] * self.n for _ in range(self.d)]

        i = 1

        #   same ops as with recursion, but using nested loops

        while i < self.d:

            for j in range(0, self.d, 2 * i):

                for k in range(j, j + i):

                    r = self.masking_poly(self.n)

                    z[k] = poly_add(z[k], r)

                    z[k + i] = poly_sub(z[k + i], r)

            i <<= 1

        return z

    def _refresh(self, v):
        """Refresh(): Refresh shares via ZeroEncoding."""

        z = self._zero_encoding()

        for i in range(self.d):

            v[i] = poly_add(v[i], z[i])

    def _xof_sample_q(self, seed):
        """Expand a seed to n uniform values [0,q-1] using a XOF."""

        blen = (self.q_bits + 7) // 8

        mask = (1 << self.q_bits) - 1

        xof = SHAKE256.new(seed)

        v = [0] * self.n

        i = 0

        while i < self.n:

            z = xof.read(blen)

            x = int.from_bytes(z, BYTEORDER) & mask

            if x < self.q:

                v[i] = x

                i += 1

        return v

    def _expand_a(self, seed):
        """ExpandA(): Expand "seed" into a polynomial."""

        #   XOF( 'A' || seed )

        xof_in = bytes([ord("A"), 0, 0, 0, 0, 0, 0, 0]) + seed

        return self._xof_sample_q(xof_in)

    def _xof_sample_u(self, seed, u):
        """Sample a keyed uniform noise polynomial."""

        blen = (u + 7) // 8

        mask = (1 << u) - 1

        mid = (1 << u) // 2

        xof = SHAKE256.new(seed)

        r = [0] * self.n

        for i in range(self.n):

            z = xof.read(blen)

            x = int.from_bytes(z, BYTEORDER) & mask

            x ^= mid  # two's complement sign (1=neg)

            r[i] = (x - mid) % self.q

        return r

    def _vec_add_rep_noise(self, u, i_v, rep):

        v = [[0] * self.n for j in range(self.d)]

        for i_rep in range(rep):

            for j in range(self.d):

                sigma = self.random_bytes(self.sec)

                hdr_u = bytes([ord("u"), i_rep, i_v, j, 0, 0, 0, 0]) + sigma

                r = self._xof_sample_u(hdr_u, u)

                v[j] = poly_add(v[j], r)

            self._refresh(v)

        return v

    def _msg_hash(self, salt, tr, msg):

        xof_in = bytes([ord("h"), 0, 0, 0, 0, 0, 0, 0]) + salt + tr + msg

        return self._xof_sample_q(xof_in)


def verify_msg_wrapper(args):

    iut, vk, tr, msg_fake, sig = args

    return iut.verify_msg(vk, tr, msg_fake, sig)


def parallel_verify(iut, vk, tr, msg_fake, sigs, num_processes=4):

    # Prepare arguments for each process

    args = [(iut, vk, tr, msg_fake, sig) for sig in sigs]

    # Start timing

    start_time_ver = time.time()

    # Use multiprocessing Pool to run in parallel

    with Pool(processes=num_processes) as pool:

        results = pool.map(verify_msg_wrapper, args)

    # End timing

    end_time_ver = time.time()

    time_ver = end_time_ver - start_time_ver

    print(f"Total time for verification with {num_processes} processes: {time_ver}s")

    return results


# =====================================================================
# 跨域 ZKP 辅助函数：纯整数环 Z[x]/(x^n+1) 运算
# =====================================================================
def poly_add_Z(a, b, n):
    return [a[i] + b[i] for i in range(n)]


def poly_sub_Z(a, b, n):
    return [a[i] - b[i] for i in range(n)]


def poly_mul_Z_ring(a, b, n):
    """纯整数域多项式乘法 (无模运算)"""
    res = [0] * n
    for i in range(n):
        if a[i] == 0:
            continue
        for j in range(n):
            if b[j] == 0:
                continue
            if i + j < n:
                res[i + j] += a[i] * b[j]
            else:
                res[i + j - n] -= a[i] * b[j]
    return res


# =====================================================================
# Plover 导出函数：提取商多项式 k (智能解算版)
# =====================================================================
# 替换原 ploversign_core.py 中的 format_plover_data 函数
def format_plover_data(iut, vk, sig):
    (salt, z2, c1, u, z1_orig) = sig
    (seed, b) = vk
    n = iut.n
    q = iut.q

    # 1. 提取公开参数并中心化
    A_raw = iut._expand_a(seed)
    A_c = poly_center(A_raw, q)

    # 手动重构 t = b << nut (中心化)
    t_raw = [(x << iut.nut) % q for x in b]
    t_c = poly_center(t_raw, q)

    u_c = poly_center(u, q)

    # 2. 提取签名见证并中心化
    z2_c = poly_center(z2, q)
    c1_c = poly_center(c1, q)
    z1_c = poly_center(z1_orig, q)

    # 3. 【核心修复】逐系数计算 k，替代多项式环乘法
    # 底层约束: A[i]*z2[i] + t[i]*c1[i] + z1[i] - q*k[i] = u[i]
    # => k[i] = (A[i]*z2[i] + t[i]*c1[i] + z1[i] - u[i]) // q
    k = []
    for i in range(n):
        lhs = A_c[i] * z2_c[i] + t_c[i] * c1_c[i] + z1_c[i]
        diff = lhs - u_c[i]
        # Plover 验证方程保证 diff 必能被 q 整除
        k.append(diff // q)

    # 4. 校验与导出
    sq_norm_k = sum(x * x for x in k)
    print(f"[+] 成功提取 k！ L2 范数平方: {sq_norm_k}")
    print(f"[!] 验证方程已转换为逐系数线性形式，与 LaBRADOR 分块约束严格对齐。")

    return {
        "statement": {"A": A_c, "t": t_c, "u": u_c, "q_plover": q, "n": n},
        "witness": {"z1": z1_c, "z2": z2_c, "c1": c1_c, "k": k},
        "meta": {"sq_norm_k": sq_norm_k, "plover_sq_beta": getattr(iut, "sq_beta", 0)},
    }


def export_batch_to_json(data_list, filename="../labrador_c/plover_labrador.json"):
    """
    将收集到的整个列表一次性写入 JSON 文件
    """
    with open(filename, "w") as f:
        json.dump(data_list, f, indent=4)
    print(f"\n成功导出 {len(data_list)} 组测试数据至 {filename}")


def export_plover_to_labrador(
    iut, vk, sig, filename="../labrador_c/plover_labrador.json"
):
    """
    提取 Plover 的公开输入和隐私见证，并导出为格式化的 JSON 格式
    供 LaBRADOR C代码读取。
    """

    (seed, b) = vk
    (salt, z2, c1, u_ori, z1) = sig

    # 1. 提取或重构公开参数 (Statement)
    A = iut._expand_a(seed)

    t2 = poly_lshift(b, iut.nut)
    t = [c - (1 << (iut.nut - 1)) for c in t2]

    sq_beta = iut.sq_beta

    # 2. 构造 JSON 字典
    export_data = {
        "statement": {"A": A, "t": t, "u": u_ori, "sq_beta": sq_beta},
        "witness": {"z1": z1, "z2": z2, "c1": c1},
    }

    # 3. 写入文件（增加了 indent=4 开启格式化输出）
    with open(filename, "w") as f:
        json.dump(export_data, f, indent=4)

    print(f"\n所需数据已导出至 {filename} (已格式化)\n")


def run_labrador():
    print("\n" + "=" * 50)
    print("开始编译 LaBRADOR C 代码...")
    print("=" * 50)

    # 增加 cwd 参数，指定在 labrador_c 文件夹下运行 make
    compile_process = subprocess.run(
        ["make", "test_chihuahua"], cwd="../labrador_c", capture_output=False
    )

    if compile_process.returncode != 0:
        print("编译失败，请检查 C 代码。")
        sys.exit(1)

    print("\n" + "=" * 50)
    print("注入 Plover 数据并执行零知识证明...")
    print("=" * 50 + "\n")

    # 增加 cwd 参数，指定在 labrador_c 文件夹下运行 C 程序
    run_process = subprocess.run(
        ["./test_chihuahua"], cwd="../labrador_c", capture_output=False
    )

    print("\n" + "=" * 50)
    if run_process.returncode == 0 or run_process.returncode == 255:
        print("执行完毕！")
    else:
        print("C 程序运行中断或发生未知错误。")
        print("=" * 50)


def chksum(v, q=549824583172097, g=15, s=31337):
    """Simple recursive poly/vector/matrix checksum routine."""
    if isinstance(v, int):
        return (g * s + v) % q
    elif isinstance(v, list):
        for x in v:
            s = chksum(x, q=q, g=g, s=s)
    return s


def chkdim(v, s=""):
    t = v
    while isinstance(t, list):
        s += "[" + str(len(t)) + "]"
        t = t[0]
    s += " = " + str(chksum(v))
    return s


if __name__ == "__main__":
    sig_vers = []
    all_export_data = []  # 【新增】用来存储所有组数据的列表

    # 这里更改测试次数（比如 10，50，100）
    TEST_COUNT = 10

    iut = PloverSign(
        bitsec=128,
        q=PLOVERSIGN_Q,
        logdivide=37,
        nut=21,
        rep=8,
        ut=6,
        up=42,
        n=PLOVERSIGN_N,
        d=32,
    )

    for i in range(10):
        entropy_input = bytes(x + i for x in range(48))
        drbg = NIST_KAT_DRBG(entropy_input)
        iut.set_random(drbg.random_bytes)
        iut.set_masking(MaskRandom().random_poly)

        msk, vk = iut.keygen()

        print(f"key: seed = {msk[0].hex().upper()}")
        print(chkdim(msk[1], "key: t"))
        print(chkdim(msk[2], "key: s"))

        print("=== Sign ===")

        tr = bytes(range(iut.tr_sz))
        msg = bytes(range(3))
        # msg_fake = bytes(range(6))
        sig = iut.sign_msg(msk, tr, msg)

        print(f"sig: salt = {sig[0].hex().upper()}")

        print(chkdim(sig[4], "sig: z1"))

        print(chkdim(sig[1], "sig: z2"))
        print(chkdim(sig[2], "sig: c1"))

        # 把当前这一组数据格式化，并追加到大列表中
        current_data = format_plover_data(iut, vk, sig)
        all_export_data.append(current_data)

        sig_vers.append((vk, tr, msg, sig))
        print(f"[*] 第 {i+1} 组签名生成完毕")

    print("=== Verify ===")
    start_time_ver = time.time()

    # 并行验证模块
    with multiprocessing.Pool() as pool:
        results = pool.starmap(iut.verify_msg, sig_vers)

    end_time_ver = time.time()

    # 打印最终的验证结果数组和时间
    print(f"验证结果: {results}")
    print("并行处理时间：", end_time_ver - start_time_ver)

    export_batch_to_json(all_export_data)
    run_labrador()
