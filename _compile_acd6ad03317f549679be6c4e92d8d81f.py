
import util
import numpy

"""blur_one_stage.py

An intentionally slow implementation of a Gaussian blur using a 3x3 kernel.

Author: Sam Prestwood
"""

import numpy as np
import numpy
import sys; sys.path += ['../../compiler']
import util
import time
import skimage
import skimage.io

def gaussian_blur(input_img, output_img):
    _argtype_values = {}
    def _log_argtype_value(id_num, v):
        try:
            if type(v) == type(_argtype_values[id_num]):
                return v
        except KeyError:
            _argtype_values[id_num] = v
            return v
        _argtype_values[id_num] = util.promote_numeric(_argtype_values[id_num], v)
        return v
    try:
    
        """Blurs the image in matrix input_img and writes the values to output_img.
    
        This uses a 3x3 Gaussian kernel to convolve with the image matrix.
    
                    1/16 2/16 1/16
        Kernel =    2/16 4/16 2/16
                    1/16 2/16 1/16
    
        For dealing with convolving along the edges of the image, we renormalize the
        kernel based on which coordinates from the kernel are in-bounds.
    
        Args:
            input_img, np.ndarray, reference to input image to blur
            output_img, np.ndarray, reference to array to save output image in
        """
        T0 = time.time()
        
        Tmid = time.time()
        
        for r in range(input_img.shape[0]):
            for c in range(0, input_img.shape[1]):
                # center
                kernel_norm = 4.0
    
                # top left
                if r > 0 and c > 0:
                    output_img[r, c] += 1.0 * input_img[r - 1, c - 1]
                    kernel_norm += 1.0
    
                # top middle
                if r > 0:
                    output_img[r, c] += 2.0 * input_img[r - 1, c    ]
                    kernel_norm += 2.0
    
                # top right
                if r > 0 and c < input_img.shape[1] - 1: 
                    output_img[r, c] += 1.0 * input_img[r - 1, c + 1]
                    kernel_norm += 1.0
    
                # left
                if c > 0:
                    output_img[r, c] += 2.0 * input_img[r    , c - 1]
                    kernel_norm += 2.0
    
                # right
                if c < input_img.shape[1] - 1:
                    output_img[r, c] += 2.0 * input_img[r    , c + 1]
                    kernel_norm += 2.0
    
                # bottom left
                if r < input_img.shape[0] - 1 and c > 0:
                    output_img[r, c] += 1.0 * input_img[r + 1, c - 1]
                    kernel_norm += 1.0
    
                # bottom middle
                if r < input_img.shape[0] - 1:
                    output_img[r, c] += 2.0 * input_img[r + 1, c    ]
                    kernel_norm += 2.0
    
                # bottom right
                if r < input_img.shape[0] - 1 and c < input_img.shape[1] - 1:
                    output_img[r, c] += 1.0 * input_img[r + 1, c + 1]
                    kernel_norm += 1.0
    
                output_img[r, c] /= kernel_norm
        print(time.time() - Tmid, Tmid - T0)
    
        return output_img
    
    
    finally:
        global _gaussian_blur_locals
        try:
            _gaussian_blur_locals
        except:
            _gaussian_blur_locals = util.TypeSignatureSet(['input_img', 'output_img'])
        _ignore_names = ['_log_argtype_value', '_argtype_values', '_ignore_names']
        _locals_typeconfig = dict([(_k, util.CythonType.from_value(_v, None, error_variable=_k)) for (_k, _v) in locals().items() if _k not in _ignore_names])
    
        _gaussian_blur_locals.add(_locals_typeconfig)

input_img = '../annotating_compiler/proj/apps/images/small_temple_rgb.png'
input_img_rgb = skimage.io.imread(input_img)
input_img_rgb = skimage.img_as_float(input_img_rgb)


def test(input_img_rgb=input_img_rgb):
    _exc = None
    try:
        def inner_func():
                
            
            ans = gaussian_blur(input_img_rgb, np.zeros(input_img_rgb.shape))
            
            return ans
        
        
        ans = inner_func()
    except Exception as _e:
        _exc = _e
    finally:
        if _exc is not None:
            raise _exc
        else:
            global _gaussian_blur_locals
            _typesL_var = {}
            if "_gaussian_blur_locals" in globals(): _typesL_var["gaussian_blur"] = util.TypeSignatureSet(['input_img', 'output_img'], [{_k: _v for (_k, _v) in _typeconfig.items() if isinstance(_k, str)} for _typeconfig in _gaussian_blur_locals])
            return {"types": _typesL_var, "test_result": ans}

if __name__ == '__main__':
    test()


